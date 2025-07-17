"""
使用Playwright下载受保护图片的模块，特别是针对字节跳动等有反爬机制的网站。
"""
import os
import time
import tempfile
import traceback
import logging
from typing import Optional
from urllib.parse import urlparse

# 如果你想看到更详细的日志，可以取消下面这行的注释
# logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

async def download_with_playwright(url: str) -> Optional[bytes]:
    """
    使用Playwright模拟真实浏览器下载文件。
    当遇到需要登录或有复杂验证的网站时，此方法非常有效。
    """
    logger.info(f"检测到特殊URL，启动Playwright下载器: {url}")
    
    try:
        from playwright.async_api import async_playwright
    except ImportError:
        logger.error("="*50)
        logger.error("错误：未安装Playwright。")
        logger.error("请在你的机器人环境的命令行中运行以下命令来安装:")
        logger.error("pip install playwright")
        logger.error("python -m playwright install")
        logger.error("="*50)
        return None
    
    async with async_playwright() as p:
        try:
            browser = await p.chromium.launch(headless=True) # 使用无头模式，后台运行
            context = await browser.new_context(
                user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
                accept_downloads=True,
                locale="zh-CN"
            )

            # --- 关键部分：为特定网站添加Cookies ---
            # 解析URL，判断是否是需要特殊处理的域名
            parsed_url = urlparse(url)
            domain = parsed_url.netloc
            
            if "byteimg.com" in domain or "dreamina.cn" in domain:
                logger.info(f"检测到字节跳动域名 ({domain})，正在添加专用Cookies...")
                #
                # TODO: 在下方[]中填入你自己的Cookies！
                # 如何获取请看我给你的教程。
                #
                cookies = [
                    {"name": "s_v_web_id", "value": "verify_mbj5u1g1_EfINGWDI_UM79_4EuE_8PW4_NvLvPdrsberm", "domain": ".byteimg.com", "path": "/"},
                    {"name": "passport_csrf_token", "value": "0e0476b9ce54257a70de0f2ea8a43703", "domain": ".byteimg.com", "path": "/"},
                    {"name": "passport_csrf_token_default", "value": "0e0476b9ce54257a70de0f2ea8a43703", "domain": ".byteimg.com", "path": "/"},
                    #{"name": "__ac_nonce", "value": "06475e3950057f1e9aac6", "domain": ".byteimg.com", "path": "/"},
                    {"name": "gd_random", "value": "eyJwZXJjZW50IjowLjY0MjI1NTAyOTQyNjMwNjIsIm1hdGNoIjp0cnVlfQ==.yj6dRWNyzvoBariNvT/htuKGGglfzTWt70I2qWzGHYU=", "domain": ".byteimg.com", "path": "/"},
                    {"name": "msToken", "value": "uzbh0QHLvdNSQf3NnOt2IBVl3-4Tao3XgwUFxRvJnSQQUlLQyM0YvRBqsXZgP6ZEPpgMpg9l_HniU1CEwIHPKfpOACDxkOxTJyRPTm7jk30=", "domain": ".byteimg.com", "path": "/"}
                ]
                
                if cookies:
                    await context.add_cookies(cookies)
                    logger.info("专用Cookies已成功添加。")
                else:
                    logger.warning("Cookies列表为空，将尝试无Cookie下载，成功率较低。")

                # 为这些域名设置特殊的请求头，模拟真实访问
                await context.set_extra_http_headers({
                    "Referer": "https://www.dreamina.cn/",
                    "Origin": "https://www.dreamina.cn",
                })

            page = await context.new_page()
            image_data = None

            try:
                # 直接访问URL并获取内容
                response = await page.goto(url, wait_until="domcontentloaded", timeout=30000)
                if response and response.ok:
                    image_data = await response.body()
                    logger.info(f"Playwright成功下载图片，大小: {len(image_data)} 字节")
                else:
                    logger.warning(f"直接访问失败，状态码: {response.status if response else '未知'}")

            except Exception as e:
                logger.error(f"Playwright下载过程中出错: {e}")

            # 如果主要方法失败，尝试备用方案：截图
            if not image_data:
                logger.info("主要下载方法失败，尝试使用截图作为备用方案...")
                try:
                    # 将页面内容替换为仅显示该图片的img标签
                    await page.set_content(f'<img src="{url}" style="margin:0; padding:0;">')
                    # 等待图片元素加载完成
                    img_element = page.locator('img')
                    await img_element.wait_for(state="visible", timeout=15000)
                    # 对该图片元素进行截图
                    image_data = await img_element.screenshot()
                    logger.info(f"备用方案（截图）成功，大小: {len(image_data)} 字节")
                except Exception as screenshot_error:
                    logger.error(f"备用方案（截图）也失败了: {screenshot_error}")

            await browser.close()
            return image_data

        except Exception as e:
            logger.error(f"Playwright启动或执行时发生严重错误: {e}")
            logger.error(traceback.format_exc())
            return None
