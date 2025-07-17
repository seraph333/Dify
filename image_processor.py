# 文件名: image_processor.py
import os
import time
import requests
from PIL import Image, ImageDraw
import io
import math
import concurrent.futures
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
import threading
import random
from loguru import logger
import hashlib
#更新日志
#2025-07-17 不验证SSL证书
class ImageProcessor:
    def __init__(self, save_dir):
        self.save_dir = save_dir
        self._ensure_save_dir()

        self.session = requests.Session()
        retry_strategy = Retry(
            total=3,
            backoff_factor=0.5,
            status_forcelist=[429, 500, 502, 503, 504]
        )
        adapter = HTTPAdapter(max_retries=retry_strategy)
        self.session.mount('https://', adapter)
        self.session.mount('http://', adapter)
        
        # 【优化】: 忽略因 verify=False 产生的 InsecureRequestWarning 警告
        from requests.packages.urllib3.exceptions import InsecureRequestWarning
        requests.packages.urllib3.disable_warnings(InsecureRequestWarning)

    def _ensure_save_dir(self):
        os.makedirs(self.save_dir, exist_ok=True)

    def _download_image(self, url, timeout=15):
        try:
            response = self.session.get(url, timeout=timeout, verify=False)
            response.raise_for_status()
            img = Image.open(io.BytesIO(response.content))
            if img.mode != 'RGB':
                img = img.convert('RGB')
            logger.info(f"图片下载成功: {url}, 原始尺寸: {img.size}")
            return img
        except Exception as e:
            logger.error(f"[ImageProcessor] 下载或打开图片失败: {url}, 错误: {e}")
            return None

    def _add_effects(self, image, radius=8, border_width=2, border_color=(240, 240, 240)):
        image_rgba = image.convert("RGBA")
        mask = Image.new('L', image_rgba.size, 0)
        draw = ImageDraw.Draw(mask)
        draw.rounded_rectangle((0, 0, image_rgba.width, image_rgba.height), radius, fill=255)
        image_rgba.putalpha(mask)
        draw = ImageDraw.Draw(image_rgba)
        draw.rounded_rectangle((0, 0, image_rgba.width - border_width, image_rgba.height - border_width), radius, outline=border_color, width=border_width)
        return image_rgba

    def _get_dynamic_background_color(self, img):
        """
        【新增核心函数】分析图片主色调，并生成一个柔和的背景色。
        """
        try:
            # 缩小图片以加快颜色分析速度
            thumbnail = img.resize((100, 100), Image.Resampling.LANCZOS)
            # 使用量化方法找到主要的几种颜色
            quantized = thumbnail.quantize(colors=16, method=Image.Quantize.MAXCOVERAGE)
            # 获取调色板中最常见的颜色
            palette = quantized.getpalette()
            color_counts = sorted(quantized.getcolors(), reverse=True)
            dominant_color_index = color_counts[0][1]
            dominant_color = tuple(palette[dominant_color_index*3:dominant_color_index*3+3])

            # 将主色调与白色混合，生成柔和的背景色 (20%主色调 + 80%白色)
            r, g, b = dominant_color
            bg_r = int(r * 0.2 + 255 * 0.8)
            bg_g = int(g * 0.2 + 255 * 0.8)
            bg_b = int(b * 0.2 + 255 * 0.8)

            logger.info(f"动态背景色生成成功: 主色调 {dominant_color} -> 背景色 {(bg_r, bg_g, bg_b)}")
            return (bg_r, bg_g, bg_b, 255)
        except Exception as e:
            logger.error(f"分析动态背景色失败: {e}，将使用默认浅灰色。")
            # 如果分析失败，返回一个安全的默认色
            return (240, 240, 240, 255)

    def _create_dynamic_grid(self, images, bg_color, line_width=4):
        """
        动态网格布局函数，现在接收一个背景色参数。
        """
        num_images = len(images)
        if num_images <= 4:
            cols = 2
        elif num_images <= 9:
            cols = 3
        else:
            cols = 4

        rows = math.ceil(num_images / cols)
        image_rows = [images[i:i+cols] for i in range(0, num_images, cols)]
        processed_rows = []
        max_row_width = 0

        for row_imgs in image_rows:
            min_height = min(img.height for img in row_imgs)
            row_width = 0
            resized_imgs_in_row = []
            for img in row_imgs:
                h = min_height
                img_ratio = img.width / img.height
                new_width = int(h * img_ratio)
                resized_img = img.resize((new_width, h), Image.Resampling.LANCZOS)
                resized_imgs_in_row.append(resized_img)
                row_width += new_width
            
            row_width += line_width * (len(row_imgs) - 1)
            max_row_width = max(max_row_width, row_width)
            processed_rows.append({"images": resized_imgs_in_row, "height": min_height, "width": row_width})

        total_height = sum(row['height'] for row in processed_rows) + line_width * (rows - 1)
        # 【使用动态背景色】
        canvas = Image.new('RGBA', (max_row_width, total_height), bg_color)

        current_y = 0
        for row_data in processed_rows:
            x_offset = (max_row_width - row_data['width']) // 2
            current_x = x_offset
            for img in row_data['images']:
                img_with_effects = self._add_effects(img)
                canvas.paste(img_with_effects, (current_x, current_y), img_with_effects)
                current_x += img.width + line_width
            current_y += row_data['height'] + line_width
            
        return canvas

    def combine_images(self, image_urls):
        """
        最终版图片合并函数，集成智能背景色功能，并优化保存逻辑。
        """
        logger.info("正在运行【智能背景最终版】的 combine_images 函数...")
        if not image_urls or len(image_urls) == 0:
            return (None, None)

        start_time = time.time()
        
        images = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(10, len(image_urls))) as executor:
            future_to_index = {executor.submit(self._download_image, url): i for i, url in enumerate(image_urls)}
            results = [None] * len(image_urls)
            for future in concurrent.futures.as_completed(future_to_index):
                index = future_to_index[future]
                try:
                    results[index] = future.result()
                except Exception as exc:
                    logger.error(f"[ImageProcessor] 下载任务索引 {index} 产生异常: {exc}")
        
        images = [img for img in results if img is not None]
        
        if not images:
            logger.error("[ImageProcessor] 没有任何图片下载成功，无法合成。")
            return (None, None)

        background_color = self._get_dynamic_background_color(images[0])

        if len(images) == 1:
            img_with_effects = self._add_effects(images[0])
            canvas = Image.new("RGBA", (img_with_effects.width + 20, img_with_effects.height + 20), background_color)
            canvas.paste(img_with_effects, (10, 10), img_with_effects)
        else:
            canvas = self._create_dynamic_grid(images, bg_color=background_color)

        if canvas:
            # 【优化点1】: 直接将带透明通道的画布转换为RGB，PIL会自动使用白色作为背景填充
            final_image = canvas.convert("RGB")

            # 【优化点2】: 将图片内容保存到内存，并计算其MD5值作为文件名
            buffer = io.BytesIO()
            final_image.save(buffer, format='JPEG', quality=95, optimize=True)
            image_content = buffer.getvalue()
            
            # 使用内容的哈希值作为文件名，避免重复保存相同图片
            md5_hash = hashlib.md5(image_content).hexdigest()
            file_name = f"{md5_hash}.jpg"
            save_path = os.path.join(self.save_dir, file_name)
            
            # 将内存中的图片内容写入文件
            with open(save_path, "wb") as f:
                f.write(image_content)
            
            buffer.seek(0) # 重置指针，以便调用方可以读取
            
            total_time = time.time() - start_time
            logger.info(f"[ImageProcessor] 图片合成完毕，永久保存至 {save_path}，总耗时: {total_time:.2f}秒")

            # 返回buffer和永久保存的路径
            return (buffer, save_path)

        return (None, None)
