import io
import json
import re
import subprocess
import tomllib
import tomlkit
from typing import Optional, Union, Dict, List, Tuple
import time
from dataclasses import dataclass, field
from datetime import datetime
import asyncio
from collections import defaultdict
from enum import Enum
import urllib.parse
import mimetypes
import base64
import uuid
import hashlib
import base64
from .image_processor import ImageProcessor

import aiohttp
import filetype
from loguru import logger
import speech_recognition as sr
import os
from WechatAPI import WechatAPIClient
from database.XYBotDB import XYBotDB
from utils.decorators import *
from utils.plugin_base import PluginBase
from gtts import gTTS
import traceback
import shutil
from PIL import Image
import xml.etree.ElementTree as ET
#from utils.config_manager import ConfigManager
# --- 新增代码开始 ---
# 尝试导入Playwright下载器，如果失败则禁用该功能
try:
    from .playwright_downloader import download_with_playwright
    has_playwright_downloader = True
    logger.info("Playwright下载器可用，将用于处理特殊图片链接。")
except ImportError:
    has_playwright_downloader = False
    logger.warning("未找到Playwright下载器或其依赖，特殊图片链接将使用标准方法下载。")
# --- 新增代码结束 ---

# 添加API代理导入
try:
    from api_manager_integrator import has_api_manager_feature
    has_api_proxy = has_api_manager_feature()
    if has_api_proxy:
        logger.info("API管理中心可用，Dify插件将使用API代理")
    else:
        logger.info("API管理中心不可用，Dify插件将使用直接连接")
except ImportError:
    has_api_proxy = False
    logger.warning("未找到API管理中心集成模块，Dify插件将使用直接连接")

# 常量定义
XYBOT_PREFIX = "----------\n"
DIFY_ERROR_MESSAGE = "🙅对不起，Dify出现错误！\n"
INSUFFICIENT_POINTS_MESSAGE = "😭你的积分不够啦！需要 {price} 积分"
VOICE_TRANSCRIPTION_FAILED = "\n语音转文字失败"
TEXT_TO_VOICE_FAILED = "\n文本转语音失败"
# 聊天室相关常量已移除

# 聊天室相关类已移除

@dataclass
class ModelConfig:
    api_key: str
    base_url: str
    trigger_words: list[str]
    price: int
    wakeup_words: list[str] = field(default_factory=list)  # 添加唤醒词列表字段

class Dify(PluginBase):
    description = "Dify插件 - 智能对话平台，支持多模型切换和会话管理"
    author = "老夏的金库"
    version = "1.7.0-21"
    #**1.7.0-21 2025-07-18** 修复当本地没有该图片时，重复引用的该图片，每次都会重复下载的问题
    #**1.7.0-20 2025-07-17** 1.不验证SSL证书,避免证书过期的网站下载图片失败。2.新增微信消息控制多图开关
    #**1.7.0-19 2025-07-15** 修复C计划引用识图后会重复保存图片的bug
    #**1.7.0-18 2025-07-15** 1.修复无法发送视频的bug。2.取消自动上传视频
    #**1.7.0-17 2025-07-14** 引用识图新增C计划：新版微信拖拽聊天记录中的图片发送时，<img>标签无md5信息，导致无法通过md5查找本地图片，C计划在保存图片前计算md5，如果xybot已保存则直接调用
    #**1.7.0-16 2025-07-14** 修复A、B计划引用识图后会重复保存图片的bug
    #**1.7.0-15 2025-07-11** 修改多图合并保存到files目录，修复单图不保存到本地的bug
    #**1.7.0-14-3 2025-07-08** 增加多图合并开关配置 by 笑·阿耶
    #**1.7.0-14-2 2025-07-08** 合并多图 by 笑·阿耶
    #**1.7.0-14-1 2025-07-08** 检测到换行符+图片链接时（豆包画图），分段回复 by 笑·阿耶
    #**1.7.0-14 2025-07-07** 修复过于严格的XML检查条件，避免引用识图失败;修改三类触发词引用消息时，无需@机器人或唤醒词即可响应
    #**1.7.0-13 2025-07-06** 使用playwright来下载豆包返回的图片，降低失败率
    #**1.7.0-12 2025-07-06** 性能提升：通过引入并发下载和二分查找压缩，机器人在处理多文件和上传大图片时更加迅速和高效。
    #**1.7.0-11 2025-07-04** 性能优化：1.预编译正则表达式（is_at_message，<think>标签） 2.使用集合（Set）进行查找secondary_triggers，提升效率
    #**1.7.0-10 2025-07-04** 修复被引用消息带@机器人时，新消息不@机器人也能触发的问题
    #**1.7.0-9 2025-07-04** 修复私聊引用图片识别
    #**1.7.0-8 2025-07-03** 修复群聊引用所有图片识别
    #**1.7.0-7 2025-07-03** 统一图片保存，webp图转换jpeg后保存并发送；统一所有图片命名，用webp图转换jpeg后的md5作为文件名；
    #**1.7.0-6 2025-07-03** 修复引用消息不@机器人/没有唤醒词也回复
    #**1.7.0-5 2025-07-02** 新增二三四类触发词，无需@机器人可直接触发
    #**1.7.0-4 2025-07-02** 修复webp图片无法引用识图
    #**1.7.0-3 2025-07-02** 修复唤醒词引用识图
    #**1.7.0-2 2025-07-01** 修复无法引用识别机器人自己发的图
    #**1.7.0-1 2025-06-27** 修复重置对话失败的bug
    # 更新版本号 - 修复Chunk too big错误，添加会话重置功能，优化GroupAtFilter兼容性
    is_ai_platform = True  # 标记为 AI 平台插件

    def _get_file_type_from_url(self, url: str) -> str:
        """
        根据URL的扩展名判断文件类型。
        返回 "image", "video", "audio", "document", "unknown"
        """
        parsed_url = urllib.parse.urlparse(url)
        path = parsed_url.path
        ext = os.path.splitext(path)[1].lower().lstrip('.')

        image_extensions = ['jpg', 'jpeg', 'png', 'gif', 'webp', 'svg', 'bmp']
        video_extensions = ['mp4', 'mov', 'mpeg', 'mpga', 'avi', 'mkv', 'flv', 'webm']
        audio_extensions = ['mp3', 'm4a', 'wav', 'webm', 'amr', 'ogg']
        document_extensions = ['txt', 'md', 'markdown', 'pdf', 'html', 'xlsx', 'xls', 'docx', 'csv', 'eml', 'msg', 'pptx', 'ppt', 'xml', 'epub']

        if ext in image_extensions:
            return "image"
        elif ext in video_extensions:
            return "video"
        elif ext in audio_extensions:
            return "audio"
        elif ext in document_extensions:
            return "document"
        else:
            # Fallback to MIME type guessing if extension is not definitive
            mime_type, _ = mimetypes.guess_type(url)
            if mime_type:
                if mime_type.startswith('image/'):
                    return "image"
                elif mime_type.startswith('video/'):
                    return "video"
                elif mime_type.startswith('audio/'):
                    return "audio"
                elif mime_type.startswith('application/') or mime_type.startswith('text/'):
                    return "document"
            return "unknown"

    async def send_segmented_text(self, bot: WechatAPIClient, message: dict, text_to_send: str, message_id=None):
        """
        【新增辅助函数】将文本按 //n 分割并逐条发送，支持文本转语音。
        """
        if not text_to_send:
            return

        to_wxid = message["FromWxid"]
        # 按 //n 分割文本，并移除空白条目
        segments = [seg.strip() for seg in text_to_send.split('//n') if seg.strip()]

        for i, segment in enumerate(segments):
            # 判断是否需要转语音发送
            if message.get("MsgType") == 34 or self.voice_reply_all:
                await self.text_to_voice_message(bot, message, text=segment, message_id=message_id)
            else:
                await bot.send_text_message(to_wxid, segment)
            
            # 在多条消息之间添加延迟，避免发送过快
            if i < len(segments) - 1:
                await asyncio.sleep(1)

    def __init__(self):
        super().__init__()
        self.user_models = {}  # 存储用户当前使用的模型
        self.processed_messages = {}  # 存储已处理的消息ID，避免重复处理
        self.message_expiry = 60  # 消息处理记录的过期时间（秒）
        try:
            with open("main_config.toml", "rb") as f:
                config = tomllib.load(f)
            self.admins = config["XYBot"]["admins"]
        except (FileNotFoundError, tomllib.TOMLDecodeError) as e:
            logger.error(f"加载主配置文件失败: {e}")
            raise

        try:
            with open("plugins/Dify/config.toml", "rb") as f:
                config = tomllib.load(f)
            plugin_config = config["Dify"]
            self.enable = plugin_config["enable"]
            self.default_model = plugin_config["default-model"]
            self.command_tip = plugin_config["command-tip"]
            self.commands = plugin_config["commands"]
            self.admin_ignore = plugin_config["admin_ignore"]
            self.whitelist_ignore = plugin_config["whitelist_ignore"]
            self.http_proxy = plugin_config["http-proxy"]
            self.voice_reply_all = plugin_config["voice_reply_all"]
            self.robot_names = plugin_config.get("robot-names", [])
            self.combine_multiple_images = plugin_config.get("combine_multiple_images", True)

            # --- 性能优化 1: 使用集合(Set)进行快速查找 ---
            # 将列表转换为集合，使 `in` 操作的平均时间复杂度从 O(n) 降为 O(1)
            self.secondary_triggers = set(plugin_config.get("secondary_triggers", []))
            
            self.tertiary_triggers = plugin_config.get("tertiary_triggers", [])
            self.quaternary_triggers = plugin_config.get("quaternary_triggers", [])
            self.remember_user_model = plugin_config.get("remember_user_model", True)
            self.support_agent_mode = plugin_config.get("support_agent_mode", True)

            self.models = {}
            for model_name, model_config in plugin_config.get("models", {}).items():
                self.models[model_name] = ModelConfig(
                    api_key=model_config["api-key"],
                    base_url=model_config["base-url"],
                    trigger_words=model_config["trigger-words"],
                    price=model_config["price"],
                    wakeup_words=model_config.get("wakeup-words", [])
                )

            self.current_model = self.models[self.default_model]
        except (FileNotFoundError, tomllib.TOMLDecodeError) as e:
            logger.error(f"加载Dify插件配置文件失败: {e}")
            raise

        self.db = XYBotDB()
        self.image_cache = {}
        self.image_cache_timeout = 60
        self.file_cache = {}
        self.file_cache_timeout = 300
        self.files_dir = "files"
        os.makedirs(self.files_dir, exist_ok=True)
        self.processor = ImageProcessor(save_dir=self.files_dir)

        self.current_agent_thoughts = {}
        self.agent_files = {}

        self.wakeup_word_to_model = {}
        logger.info("开始加载唤醒词配置:")
        for model_name, model_config in self.models.items():
            logger.info(f"处理模型 '{model_name}' 的唤醒词列表: {model_config.wakeup_words}")
            for wakeup_word in model_config.wakeup_words:
                if wakeup_word in self.wakeup_word_to_model:
                    old_model = next((name for name, config in self.models.items()
                                     if config == self.wakeup_word_to_model[wakeup_word]), '未知')
                    logger.warning(f"唤醒词冲突! '{wakeup_word}' 已绑定到模型 '{old_model}'，"
                                  f"现在被覆盖绑定到 '{model_name}'")
                self.wakeup_word_to_model[wakeup_word] = model_config
                logger.info(f"唤醒词 '{wakeup_word}' 成功绑定到模型 '{model_name}'")

        logger.info(f"唤醒词映射完成，共加载 {len(self.wakeup_word_to_model)} 个唤醒词")

        self.config_path = os.path.join(os.path.dirname(__file__), "config.toml")
        logger.info(f"加载Dify插件配置文件：{self.config_path}")

        # --- 性能优化 2: 预编译正则表达式 ---
        # 避免在函数调用或循环中重复编译，提升性能
        self.think_pattern = re.compile(r'<think>.*?</think>', re.DOTALL)
        self.at_patterns = {name: re.compile(f'@{re.escape(name)}\\b') for name in self.robot_names}

        self.api_proxy = None
        if has_api_proxy:
            try:
                import sys
                sys.path.append(os.path.join(os.path.dirname(__file__), "..", ".."))
                from admin.server import get_api_proxy
                self.api_proxy = get_api_proxy()
                if self.api_proxy:
                    logger.info("成功获取API代理实例")
                else:
                    logger.warning("API代理实例获取失败，将使用直接连接")
            except Exception as e:
                logger.error(f"获取API代理实例失败: {e}")
                logger.error(traceback.format_exc())

        # --- 性能优化：为高资源消耗的Playwright任务创建并发限制器 ---
        # 限制同时运行的Playwright实例数量，防止服务器资源耗尽
        # 这个值可以根据你的服务器配置调整，2或3是比较安全的选择
        self.playwright_semaphore = asyncio.Semaphore(2) 

    async def _update_config_and_save(self, key: str, value: bool) -> bool:
        """
        【优化版】一个安全的函数，用于更新内存中的配置和config.toml文件。
        使用 tomlkit 来保留注释和格式。
        """
        # 1. 更新内存中的设置，立即生效
        if key == "combine_multiple_images":
            self.combine_multiple_images = value
            logger.info(f"内存中的配置 'combine_multiple_images' 已更新为: {value}")
        else:
            logger.warning(f"不支持动态修改配置项: {key}")
            return False
    
        # 2. 将修改写回 config.toml 文件，使其永久生效
        try:
            # 使用 'tomlkit' 库读取现有配置，它会保留所有格式
            with open(self.config_path, "r", encoding="utf-8") as f:
                config_data = tomlkit.load(f)
    
            # 修改字典中的值
            config_data["Dify"][key] = value
    
            # 将修改后的整个配置写回文件，格式将被保留
            with open(self.config_path, "w", encoding="utf-8") as f:
                tomlkit.dump(config_data, f)
            
            logger.success(f"成功将配置 '{key} = {value}' 保存到 {self.config_path}")
            return True
        except FileNotFoundError:
            logger.error(f"配置文件未找到: {self.config_path}")
            return False
        except Exception as e:
            logger.error(f"更新配置文件时发生错误: {e}")
            return False

    async def _save_image_and_get_md5(self, image_content: bytes) -> Optional[tuple[str, bytes]]:
        """
        统一处理图片，返回最终JPEG内容的MD5和二进制内容，但不再直接保存文件。
        保存操作将由调用方根据需要决定。
        1. 将任何格式的图片转换为JPEG。
        2. 计算JPEG内容的MD5。
        3. 返回 (MD5值, JPEG二进制内容) 的元组。
        """
        if not image_content:
            logger.error("图片内容为空，无法处理。")
            return None
        try:
            with Image.open(io.BytesIO(image_content)) as img:
                # 统一转换为RGB模式以去除alpha通道（适用于PNG, WEBP等）
                if img.mode in ('RGBA', 'LA', 'P'):
                    if img.mode == 'P':
                        img = img.convert('RGBA')
                    background = Image.new('RGB', img.size, (255, 255, 255))
                    background.paste(img, mask=img.split()[-1])
                    img = background
                elif img.mode != 'RGB':
                    img = img.convert('RGB')

                # 将处理后的图片保存到内存中的BytesIO对象
                output_buffer = io.BytesIO()
                img.save(output_buffer, format='JPEG', quality=95)
                jpeg_content = output_buffer.getvalue()

                # 计算最终JPEG内容的MD5
                md5_hash = hashlib.md5(jpeg_content).hexdigest()
                
                # 注意：这里不再保存文件，只返回处理结果
                # logger.info(f"图片已在内存中统一处理，MD5为: {md5_hash}")
                return md5_hash, jpeg_content
        except Exception as e:
            logger.error(f"统一处理图片时发生错误: {e}")
            logger.error(traceback.format_exc())
            return None

    def get_user_model(self, user_id: str) -> ModelConfig:
        """获取用户当前使用的模型"""
        if self.remember_user_model and user_id in self.user_models:
            return self.user_models[user_id]
        return self.current_model

    def set_user_model(self, user_id: str, model: ModelConfig):
        """设置用户当前使用的模型"""
        if self.remember_user_model:
            self.user_models[user_id] = model

    def is_message_processed(self, message: dict) -> bool:
        """检查消息是否已经处理过"""
        # 清理过期的消息记录
        current_time = time.time()
        expired_keys = []
        for msg_id, timestamp in self.processed_messages.items():
            if current_time - timestamp > self.message_expiry:
                expired_keys.append(msg_id)

        for key in expired_keys:
            del self.processed_messages[key]

        # 获取消息ID
        msg_id = message.get("MsgId") or message.get("NewMsgId")
        if not msg_id:
            return False  # 如果没有消息ID，视为未处理过

        # 检查消息是否已处理
        return msg_id in self.processed_messages

    def mark_message_processed(self, message: dict):
        """标记消息为已处理"""
        msg_id = message.get("MsgId") or message.get("NewMsgId")
        if msg_id:
            self.processed_messages[msg_id] = time.time()
            logger.debug(f"标记消息 {msg_id} 为已处理")

    def get_model_from_message(self, content: str, user_id: str) -> tuple[ModelConfig, str, bool]:
        """根据消息内容判断使用哪个模型，并返回是否是切换模型的命令"""
        original_content = content  # 保留原始内容
        content = content.lower()  # 只在检测时使用小写版本

        # 检查是否是切换模型的命令
        if content.endswith("切换"):
            for model_name, model_config in self.models.items():
                for trigger in model_config.trigger_words:
                    if content.startswith(trigger.lower()):
                        self.set_user_model(user_id, model_config)
                        logger.info(f"用户 {user_id} 切换模型到 {model_name}")
                        return model_config, "", True
            return self.get_user_model(user_id), original_content, False

        # 检查是否使用了唤醒词
        logger.debug(f"检查消息 '{content}' 是否包含唤醒词")
        for wakeup_word, model_config in self.wakeup_word_to_model.items():
            wakeup_lower = wakeup_word.lower()
            content_lower = content.lower()
            if content_lower.startswith(wakeup_lower) or f" {wakeup_lower}" in content_lower:
                model_name = next((name for name, config in self.models.items() if config == model_config), '未知')
                logger.info(f"消息中检测到唤醒词 '{wakeup_word}'，临时使用模型 '{model_name}'")

                # 更精确地替换唤醒词
                # 先找到原文中唤醒词的实际位置和形式
                original_wakeup = None
                if content_lower.startswith(wakeup_lower):
                    # 如果以唤醒词开头，直接取对应长度的原始文本
                    original_wakeup = original_content[:len(wakeup_lower)]
                else:
                    # 如果唤醒词在中间，找到它的位置并获取原始形式
                    wakeup_pos = content_lower.find(f" {wakeup_lower}") + 1  # +1 是因为包含了前面的空格
                    if wakeup_pos > 0:
                        original_wakeup = original_content[wakeup_pos:wakeup_pos+len(wakeup_lower)]

                if original_wakeup:
                    # 使用原始形式进行替换，保留大小写
                    query = original_content.replace(original_wakeup, "", 1).strip()
                    logger.debug(f"唤醒词处理后的查询: '{query}'")
                    return model_config, query, False

        # 检查是否是临时使用其他模型
        for model_name, model_config in self.models.items():
            for trigger in model_config.trigger_words:
                if trigger.lower() in content:
                    logger.info(f"消息中包含触发词 '{trigger}'，临时使用模型 '{model_name}'")
                    query = original_content.replace(trigger, "", 1).strip()  # 使用原始内容替换原始触发词
                    return model_config, query, False

        # 使用用户当前的模型
        current_model = self.get_user_model(user_id)
        model_name = next((name for name, config in self.models.items() if config == current_model), '默认')
        logger.debug(f"未检测到特定模型指示，使用用户 {user_id} 当前默认模型 '{model_name}'")
        return current_model, original_content, False

    async def check_and_notify_inactive_users(self, bot: WechatAPIClient):
        # 聊天室功能已移除
        return

    # 聊天室相关方法已移除
    """
    async def reset_conversation(self, bot: WechatAPIClient, message: dict, model_config=None):
        #重置与Dify的对话

        #Args:
           # bot: WechatAPIClient实例
           # message: 消息字典
           # model_config: 模型配置（可选）

        #Returns:
            #bool: 是否成功重置对话
        
        try:
            # 使用传入的model_config，如果没有则使用默认模型
            model = model_config or self.current_model

            # 获取用户ID
            user_id = message["FromWxid"]
            if message.get("IsGroup", False):
                # 群聊消息，使用群聊ID
                user_id = message["FromWxid"]
            else:
                # 私聊消息，使用发送者ID
                user_id = message["SenderWxid"]

            # 从数据库获取会话ID
            conversation_id = self.db.get_llm_thread_id(user_id, "dify")

            if not conversation_id:
                logger.info(f"用户 {user_id} 没有活跃的对话，无需重置")
                return False

            logger.info(f"准备重置用户 {user_id} 的对话，会话ID: {conversation_id}")

            # 构建API请求
            url = f"{model.base_url}/conversations/{conversation_id}"
            headers = {"Authorization": f"Bearer {model.api_key}", "Content-Type": "application/json"}
            data = {"user": user_id}

            # 发送DELETE请求
            async with aiohttp.ClientSession() as session:
                # 正确的方式是在请求时设置代理，而不是在创建会话时
                proxy = self.http_proxy if self.http_proxy and self.http_proxy.strip() else None
                async with session.delete(url, headers=headers, json=data, proxy=proxy) as resp:
                    if resp.status in (200, 201, 204):
                        try:
                            result = await resp.json()
                            logger.debug(f"重置对话API响应: {result}")
                            if result and result.get("result") == "success":
                                # 重置成功，清除数据库中的会话ID
                                self.db.save_llm_thread_id(user_id, "", "dify")
                                logger.success(f"成功重置用户 {user_id} 的对话")
                                return True
                            else:
                                logger.error(f"重置对话失败，API返回: {result}")
                        except Exception as json_error:
                            # 如果JSON解析失败，但状态码是成功的，仍然认为重置成功
                            logger.warning(f"重置对话响应JSON解析失败，但状态码成功: {json_error}")
                            response_text = await resp.text()
                            logger.debug(f"响应内容: {response_text}")

                            # 如果状态码是204（No Content），通常表示删除成功
                            if resp.status == 204:
                                self.db.save_llm_thread_id(user_id, "", "dify")
                                logger.success(f"成功重置用户 {user_id} 的对话（状态码204）")
                                return True
                    else:
                        error_text = await resp.text()
                        logger.error(f"重置对话失败: HTTP {resp.status} - {error_text}")

            return False
        except Exception as e:
            logger.error(f"重置对话时发生错误: {e}")
            logger.error(traceback.format_exc())
            return False
    """
    async def reset_conversation(self, bot: WechatAPIClient, message: dict, model_config=None):
        """重置与Dify的对话

        Args:
            bot: WechatAPIClient实例
            message: 消息字典
            model_config: 模型配置（可选）

        Returns:
            bool: 是否成功重置对话
        """
        try:
            # 使用传入的model_config，如果没有则使用默认模型
            model = model_config or self.current_model

            # 获取用户ID
            user_id = message["FromWxid"]
            if message.get("IsGroup", False):
                # 群聊消息，使用群聊ID
                user_id = message["FromWxid"]
            else:
                # 私聊消息，使用发送者ID
                user_id = message["SenderWxid"]

            # 从数据库获取会话ID
            conversation_id = self.db.get_llm_thread_id(user_id, "dify")

            if not conversation_id:
                logger.info(f"用户 {user_id} 没有活跃的对话，无需重置")
                return False

            logger.info(f"准备重置用户 {user_id} 的对话，会话ID: {conversation_id}")

            # 构建API请求
            url = f"{model.base_url}/conversations/{conversation_id}"
            headers = {"Authorization": f"Bearer {model.api_key}", "Content-Type": "application/json"}
            data = {"user": user_id}

            # 发送DELETE请求
            async with aiohttp.ClientSession() as session:
                # 正确的方式是在请求时设置代理，而不是在创建会话时
                proxy = self.http_proxy if self.http_proxy and self.http_proxy.strip() else None
                async with session.delete(url, headers=headers, json=data, proxy=proxy) as resp:
                    if resp.status in (200, 201, 204):
                        # 对于204 No Content响应，不需要尝试解析JSON
                        if resp.status == 204:
                            # 204表示删除成功但无返回内容
                            self.db.save_llm_thread_id(user_id, "", "dify")
                            logger.success(f"成功重置用户 {user_id} 的对话 (状态码: 204)")
                            return True
                        else:
                            try:
                                result = await resp.json()
                                if result.get("result") == "success":
                                    # 重置成功，清除数据库中的会话ID
                                    self.db.save_llm_thread_id(user_id, "", "dify")
                                    logger.success(f"成功重置用户 {user_id} 的对话")
                                    return True
                                else:
                                    logger.error(f"重置对话失败，API返回: {result}")
                            except Exception as json_error:
                                logger.error(f"解析JSON失败，但状态码为成功: {json_error}")
                                # 状态码是成功的，尽管JSON解析失败，我们认为操作成功
                                self.db.save_llm_thread_id(user_id, "", "dify")
                                logger.success(f"成功重置用户 {user_id} 的对话 (JSON解析失败但状态码成功)")
                                return True
                    elif resp.status == 404:
                        error_text = await resp.text()
                        logger.info(f"对话不存在 (404): {error_text}")
                        # 如果对话不存在，我们也应该清除数据库中的会话ID
                        self.db.save_llm_thread_id(user_id, "", "dify")
                        # 返回True表示"重置"成功 - 因为最终目的是确保没有活跃的对话
                        return True
                    else:
                        error_text = await resp.text()
                        logger.error(f"重置对话失败: HTTP {resp.status} - {error_text}")

            return False
        except Exception as e:
            logger.error(f"重置对话时发生错误: {e}")
            logger.error(traceback.format_exc())
            return False

    async def simple_reset_conversation(self, bot: WechatAPIClient, message: dict, model_config=None):
        """简单重置对话：直接清除数据库中的会话ID

        Args:
            bot: WechatAPIClient实例
            message: 消息字典
            model_config: 模型配置（可选）

        Returns:
            bool: 是否成功重置对话
        """
        try:
            # 获取用户ID
            user_id = message["FromWxid"]
            if message.get("IsGroup", False):
                # 群聊消息，使用群聊ID
                user_id = message["FromWxid"]
            else:
                # 私聊消息，使用发送者ID
                user_id = message["SenderWxid"]

            # 从数据库获取会话ID
            conversation_id = self.db.get_llm_thread_id(user_id, "dify")

            if not conversation_id:
                logger.info(f"用户 {user_id} 没有活跃的对话，创建新会话")
            else:
                logger.info(f"准备重置用户 {user_id} 的对话，会话ID: {conversation_id}")

            # 直接清除数据库中的会话ID
            self.db.save_llm_thread_id(user_id, "", "dify")
            logger.success(f"成功重置用户 {user_id} 的对话")
            return True

        except Exception as e:
            logger.error(f"简单重置对话时发生错误: {e}")
            logger.error(traceback.format_exc())
            return False

    @on_text_message(priority=20)
    async def handle_text(self, bot: WechatAPIClient, message: dict):
        if not self.enable:
            return

        content = message["Content"].strip()
        # --- 新增代码开始：处理管理员指令 ---
        sender_wxid = message["SenderWxid"]
        # 检查发消息的人是否是管理员
        if sender_wxid in self.admins:
            if content == "开启多图合并":
                success = await self._update_config_and_save("combine_multiple_images", True)
                reply = "✅ 多图合并功能已开启。" if success else "❌ 开启失败，请查看后台日志。"
                await bot.send_text_message(message["FromWxid"], reply)
                return # 处理完毕，不再执行后续逻辑
            
            elif content == "关闭多图合并":
                success = await self._update_config_and_save("combine_multiple_images", False)
                reply = "✅ 多图合并功能已关闭，将逐张发送图片。" if success else "❌ 关闭失败，请查看后台日志。"
                await bot.send_text_message(message["FromWxid"], reply)
                return # 处理完毕，不再执行后续逻辑
        # --- 新增代码结束 ---

        command = content.split(" ")[0] if content else ""

        await self.check_and_notify_inactive_users(bot)

        # 处理重置对话命令
        if command == "重置对话":
            # 获取用户当前使用的模型
            model = self.get_user_model(message["SenderWxid"])

            # 执行重置对话操作
            success = await self.reset_conversation(bot, message, model)

            if success:
                # 重置成功，发送通知
                if message.get("IsGroup", False):
                    await bot.send_at_message(
                        message["FromWxid"],
                        "\n对话已重置，我已经忘记了之前的对话内容。",
                        [message["SenderWxid"]]
                    )
                else:
                    await bot.send_text_message(
                        message["FromWxid"],
                        "对话已重置，我已经忘记了之前的对话内容。"
                    )
            else:
                # 重置失败，发送通知
                if message.get("IsGroup", False):
                    await bot.send_at_message(
                        message["FromWxid"],
                        "\n重置对话失败，可能是因为没有活跃的对话或发生了错误。",
                        [message["SenderWxid"]]
                    )
                else:
                    await bot.send_text_message(
                        message["FromWxid"],
                        "重置对话失败，可能是因为没有活跃的对话或发生了错误。"
                    )
            return

        if not message["IsGroup"]:
            # 二类触发词：完全匹配
            if content in self.secondary_triggers:
                logger.info(f"检测到二类触发词: {content}")
                model = self.get_user_model(message["SenderWxid"])
                await self.dify(bot, message, content, specific_model=model)
                return

            # 三类触发词：以...开头
            for trigger in self.tertiary_triggers:
                if content.startswith(trigger):
                    logger.info(f"检测到三类触发词: {trigger}")
                    model = self.get_user_model(message["SenderWxid"])
                    await self.dify(bot, message, content, specific_model=model)
                    return

            # 四类触发词：以...结尾
            for trigger in self.quaternary_triggers:
                if content.endswith(trigger):
                    logger.info(f"检测到四类触发词: {trigger}")
                    model = self.get_user_model(message["SenderWxid"])
                    await self.dify(bot, message, content, specific_model=model)
                    return

            # 先检查唤醒词或触发词，获取对应模型
            model, processed_query, is_switch = self.get_model_from_message(content, message["SenderWxid"])

            # 检查是否是重置会话命令
            if processed_query.strip().lower() in ["重置会话", "重置对话", "新对话", "清空对话", "reset"]:
                success = await self.simple_reset_conversation(bot, message, model_config=model)
                if success:
                    await bot.send_text_message(
                        message["FromWxid"],
                        f"{XYBOT_PREFIX}✅ 已重置对话，开始新的会话！"
                    )
                else:
                    await bot.send_text_message(
                        message["FromWxid"],
                        f"{XYBOT_PREFIX}❌ 重置对话失败，请稍后重试。"
                    )
                return

            # 检查是否有最近的图片
            image_content = await self.get_cached_image(message["FromWxid"])
            files = []
            if image_content:
                try:
                    logger.debug("发现最近的图片，准备上传到 Dify")
                    file_id = await self.upload_file_to_dify(
                        image_content,
                        f"image_{int(time.time())}.jpg",  # 生成一个有效的文件名
                        "image/jpeg",  # 根据实际图片类型调整
                        message["FromWxid"],
                        model_config=model  # 传递正确的模型配置
                    )
                    if file_id:
                        logger.debug(f"图片上传成功，文件ID: {file_id}")
                        files = [file_id]
                    else:
                        logger.error("图片上传失败")
                except Exception as e:
                    logger.error(f"处理图片失败: {e}")

            if command in self.commands:
                query = content[len(command):].strip()
            else:
                query = content

            # 检查API密钥是否可用 - 使用检测到的模型，而非默认模型
            if query and model.api_key:
                if await self._check_point(bot, message, model):  # 传递模型到_check_point
                    if is_switch:
                        model_name = next(name for name, config in self.models.items() if config == model)
                        await bot.send_text_message(
                            message["FromWxid"],
                            f"已切换到{model_name.upper()}模型，将一直使用该模型直到下次切换。"
                        )
                        return
                    # 使用获取到的模型处理请求
                    await self.dify(bot, message, processed_query, files=files, specific_model=model)
                else:
                    logger.info(f"积分检查失败或模型API密钥无效，无法处理请求")
            else:
                if not query:
                    logger.debug("查询内容为空，不处理")
                elif not model.api_key:
                    logger.error(f"模型 {next((name for name, config in self.models.items() if config == model), '未知')} 的API密钥未配置")
                    await bot.send_text_message(message["FromWxid"], "所选模型的API密钥未配置，请联系管理员")
            return

        # 以下是群聊处理逻辑
        group_id = message["FromWxid"]
        user_wxid = message["SenderWxid"]

        # 二类触发词：完全匹配
        if content in self.secondary_triggers:
            logger.info(f"群聊检测到二类触发词: {content}")
            model = self.get_user_model(user_wxid)
            await self.dify(bot, message, content, specific_model=model)
            return

        # 三类触发词：以...开头
        for trigger in self.tertiary_triggers:
            if content.startswith(trigger):
                logger.info(f"群聊检测到三类触发词: {trigger}")
                model = self.get_user_model(user_wxid)
                await self.dify(bot, message, content, specific_model=model)
                return

        # 四类触发词：以...结尾
        for trigger in self.quaternary_triggers:
            if content.endswith(trigger):
                logger.info(f"群聊检测到四类触发词: {trigger}")
                model = self.get_user_model(user_wxid)
                await self.dify(bot, message, content, specific_model=model)
                return

        # 检查GroupAtFilter插件添加的响应标记
        needs_response = message.get("NeedsResponse", False)
        triggered_by = message.get("TriggeredBy", "")

        if self.enable and needs_response:
            logger.info(f"[Dify] 检测到GroupAtFilter标记的群聊消息，触发方式: {triggered_by}")
            # 这是GroupAtFilter标记的需要响应的群聊消息
            # 内容已经被GroupAtFilter清理过了，直接处理
            query = content
            files = []  # 初始化files变量

            # 获取用户当前使用的模型
            model = self.get_user_model(user_wxid)

            # 检查是否有唤醒词或触发词
            model, processed_query, is_switch = self.get_model_from_message(query, user_wxid)

            # 检查是否是重置会话命令
            if processed_query.strip().lower() in ["重置会话", "重置对话", "新对话", "清空对话", "reset"]:
                success = await self.simple_reset_conversation(bot, message, model_config=model)
                if success:
                    await bot.send_text_message(
                        message["FromWxid"],
                        f"{XYBOT_PREFIX}✅ 已重置对话，开始新的会话！"
                    )
                else:
                    await bot.send_text_message(
                        message["FromWxid"],
                        f"{XYBOT_PREFIX}❌ 重置对话失败，请稍后重试。"
                    )
                return

            if is_switch:
                model_name = next(name for name, config in self.models.items() if config == model)
                await bot.send_at_message(
                    group_id,
                    f"\n已切换到{model_name.upper()}模型，将一直使用该模型直到下次切换。",
                    [user_wxid]
                )
                return

            # 检查模型API密钥是否可用
            if model.api_key and await self._check_point(bot, message, model):
                logger.info(f"[Dify] 使用模型 '{next((name for name, config in self.models.items() if config == model), '未知')}' 处理GroupAtFilter标记的消息")
                await self.dify(bot, message, processed_query, files=files, specific_model=model)
            else:
                logger.info(f"[Dify] 积分检查失败或API密钥未配置，无法处理GroupAtFilter标记的消息")
            return

        # 添加对切换模型命令的特殊处理
        if content.endswith("切换"):
            for model_name, model_config in self.models.items():
                for trigger in model_config.trigger_words:
                    if content.lower().startswith(trigger.lower()):
                        self.set_user_model(user_wxid, model_config)
                        await bot.send_at_message(
                            group_id,
                            f"\n已切换到{model_name.upper()}模型，将一直使用该模型直到下次切换。",
                            [user_wxid]
                        )
                        return

        # 处理群聊中的重置对话命令
        if command == "重置对话":
            # 获取用户当前使用的模型
            model = self.get_user_model(user_wxid)

            # 执行重置对话操作
            success = await self.reset_conversation(bot, message, model)

            if success:
                # 重置成功，发送通知
                await bot.send_at_message(
                    group_id,
                    "\n对话已重置，我已经忘记了之前的对话内容。",
                    [user_wxid]
                )
            else:
                # 重置失败，发送通知
                await bot.send_at_message(
                    group_id,
                    "\n重置对话失败，可能是因为没有活跃的对话或发生了错误。",
                    [user_wxid]
                )
            return

        is_at = self.is_at_message(message)
        is_command = command in self.commands

        # 先检查是否有唤醒词
        wakeup_detected = False
        wakeup_model = None
        processed_wakeup_query = ""

        for wakeup_word, model_config in self.wakeup_word_to_model.items():
            # 改用更精确的匹配方式，避免错误识别
            wakeup_lower = wakeup_word.lower()
            content_lower = content.lower()
            if content_lower.startswith(wakeup_lower) or f" {wakeup_lower}" in content_lower:
                wakeup_detected = True
                wakeup_model = model_config
                model_name = next((name for name, config in self.models.items() if config == model_config), '未知')
                logger.info(f"检测到唤醒词 '{wakeup_word}'，触发模型 '{model_name}'，原始内容: '{content}'")

                # 更精确地替换唤醒词
                original_wakeup = None
                if content_lower.startswith(wakeup_lower):
                    original_wakeup = content[:len(wakeup_lower)]
                else:
                    wakeup_pos = content_lower.find(f" {wakeup_lower}") + 1
                    if wakeup_pos > 0:
                        original_wakeup = content[wakeup_pos:wakeup_pos+len(wakeup_lower)]

                if original_wakeup:
                    processed_wakeup_query = content.replace(original_wakeup, "", 1).strip()
                    logger.info(f"处理后的查询内容: '{processed_wakeup_query}'")
                break

        # 检查是否是重置会话命令
        if processed_wakeup_query.strip().lower() in ["重置会话", "重置对话", "新对话", "清空对话", "reset"]:
            success = await self.simple_reset_conversation(bot, message, model_config=wakeup_model or self.get_user_model(user_wxid))
            if success:
                await bot.send_text_message(
                    message["FromWxid"],
                    f"{XYBOT_PREFIX}✅ 已重置对话，开始新的会话！"
                )
            else:
                await bot.send_text_message(
                    message["FromWxid"],
                    f"{XYBOT_PREFIX}❌ 重置对话失败，请稍后重试。"
                )
            return

        # 检查是否有最近的图片 - 无论聊天室功能是否启用都获取图片
        files = []
        image_content = await self.get_cached_image(group_id)
        if image_content:
            try:
                logger.debug("发现最近的图片，准备上传到 Dify")
                # 如果检测到唤醒词，使用对应模型；否则使用用户当前模型
                model_config = wakeup_model or self.get_user_model(user_wxid)

                file_id = await self.upload_file_to_dify(
                    image_content,
                    f"image_{int(time.time())}.jpg",  # 生成一个有效的文件名
                    "image/jpeg",
                    group_id,
                    model_config=model_config  # 传递正确的模型配置
                )
                if file_id:
                    logger.debug(f"图片上传成功，文件ID: {file_id}")
                    files = [file_id]
                else:
                    logger.error("图片上传失败")
            except Exception as e:
                logger.error(f"处理图片失败: {e}")

        # 如果检测到唤醒词，处理唤醒词请求
        if wakeup_detected and wakeup_model and processed_wakeup_query:
            # 如果是引用消息，直接跳过，让 on_quote_message 处理器来处理
            if message.get("Quote") or message.get("MsgType") in [49, 57]:
                logger.info("handle_text检测到带唤醒词的引用消息，交由handle_quote处理。")
                return True

            if wakeup_model.api_key:
                if await self._check_point(bot, message, wakeup_model):
                    logger.info(f"使用唤醒词对应模型处理文本消息请求")
                    await self.dify(bot, message, processed_wakeup_query, files=files, specific_model=wakeup_model)
                else:
                    logger.info(f"积分检查失败，无法处理唤醒词请求")
            else:
                model_name = next((name for name, config in self.models.items() if config == wakeup_model), '未知')
                logger.error(f"唤醒词对应模型 '{model_name}' 的API密钥未配置")
                if message.get("IsGroup"):
                    await bot.send_at_message(group_id, f"\n此模型API密钥未配置，请联系管理员", [user_wxid])
                else:
                    await bot.send_text_message(message["FromWxid"], "此模型API密钥未配置，请联系管理员")
            return

        # 继续处理@或命令的情况
        if is_at or is_command:
            # 群聊处理逻辑
            query = content
            for robot_name in self.robot_names:
                query = query.replace(f"@{robot_name}", "").strip()
            if command in self.commands:
                query = query[len(command):].strip()
            if query:
                # 获取用户当前使用的模型
                model = self.get_user_model(message["SenderWxid"])
                if await self._check_point(bot, message, model):
                    # 检查是否有唤醒词或触发词
                    model, processed_query, is_switch = self.get_model_from_message(query, message["SenderWxid"])
                    await self.dify(bot, message, processed_query, files=files, specific_model=model)
            return

        # 聊天室功能已移除，所有消息都需要@或命令触发
        if is_at or is_command:
            query = content
            for robot_name in self.robot_names:
                query = query.replace(f"@{robot_name}", "").strip()
            if command in self.commands:
                query = query[len(command):].strip()
            if query:
                # 获取用户当前使用的模型
                model = self.get_user_model(message["SenderWxid"])
                if await self._check_point(bot, message, model):
                    await self.dify(bot, message, query, files=files, specific_model=model)
        return

        if content:
            if is_at or is_command:
                query = content

                # 检查是否以@开头，如果是，则移除@部分
                if content.startswith('@'):
                    # 先检查是否是@机器人
                    at_bot_prefix = None
                    for robot_name in self.robot_names:
                        if content.startswith(f'@{robot_name}'):
                            at_bot_prefix = f'@{robot_name}'
                            break

                    if at_bot_prefix:
                        # 如果是@机器人，移除@机器人部分
                        query = content[len(at_bot_prefix):].strip()
                        logger.debug(f"移除@{at_bot_prefix}后的查询内容: {query}")
                    else:
                        # 如果不是@机器人，则尝试找第一个空格
                        space_index = content.find(' ')
                        if space_index > 0:
                            # 保留第一个空格后面的所有内容
                            query = content[space_index+1:].strip()
                            logger.debug(f"移除@前缀后的查询内容: {query}")
                        else:
                            # 如果没有空格，尝试提取@后面的内容
                            # 找到第一个非空格字符的位置
                            for i in range(1, len(content)):
                                if content[i] != '@' and content[i] != ' ':
                                    query = content[i:].strip()
                                    logger.debug(f"提取@后面的内容: {query}")
                                    break
                            else:
                                # 如果整个内容都是@，将query设为空
                                query = ""
                else:
                    # 如果不是以@开头，则尝试移除@机器人名称
                    for robot_name in self.robot_names:
                        query = query.replace(f"@{robot_name}", "").strip()
                if command in self.commands:
                    query = query[len(command):].strip()
                if query:
                    # 获取用户当前使用的模型
                    model = self.get_user_model(message["SenderWxid"])
                    if await self._check_point(bot, message, model):
                        # 检查是否有唤醒词或触发词
                        model, processed_query, is_switch = self.get_model_from_message(query, message["SenderWxid"])
                        if is_switch:
                            model_name = next(name for name, config in self.models.items() if config == model)
                            await bot.send_at_message(
                                message["FromWxid"],
                                f"\n已切换到{model_name.upper()}模型，将一直使用该模型直到下次切换。",
                                [message["SenderWxid"]]
                            )
                            return
                        await self.dify(bot, message, processed_query, files=files, specific_model=model)
            else:
                # 只有在聊天室功能开启时，才缓冲普通消息
                if self.chatroom_enable:
                    await self.chat_manager.add_message_to_buffer(group_id, user_wxid, content, files)
                    await self.schedule_message_processing(bot, group_id, user_wxid)
        return
    
    @on_at_message(priority=20)
    async def handle_at(self, bot: WechatAPIClient, message: dict):
        if not self.enable:
            return

        if not self.current_model.api_key:
            await bot.send_at_message(message["FromWxid"], "\n你还没配置Dify API密钥！", [message["SenderWxid"]])
            return False

        await self.check_and_notify_inactive_users(bot)

        content = message["Content"].strip()
        query = content

        # 检查是否是重置对话命令
        command = content.split(" ")[0] if content else ""
        if command == "重置对话":
            # 获取用户当前使用的模型
            model = self.get_user_model(message["SenderWxid"])

            # 执行重置对话操作
            success = await self.reset_conversation(bot, message, model)

            if success:
                # 重置成功，发送通知
                await bot.send_at_message(
                    message["FromWxid"],
                    "\n对话已重置，我已经忘记了之前的对话内容。",
                    [message["SenderWxid"]]
                )
            else:
                # 重置失败，发送通知
                await bot.send_at_message(
                    message["FromWxid"],
                    "\n重置对话失败，可能是因为没有活跃的对话或发生了错误。",
                    [message["SenderWxid"]]
                )
            return

        # 检查是否以@开头，如果是，则移除@部分
        if content.startswith('@'):
            # 先检查是否是@机器人
            at_bot_prefix = None
            for robot_name in self.robot_names:
                if content.startswith(f'@{robot_name}'):
                    at_bot_prefix = f'@{robot_name}'
                    break

            if at_bot_prefix:
                # 如果是@机器人，移除@机器人部分
                query = content[len(at_bot_prefix):].strip()
                logger.debug(f"移除@{at_bot_prefix}后的查询内容: {query}")
            else:
                # 如果不是@机器人，则尝试找第一个空格
                space_index = content.find(' ')
                if space_index > 0:
                    # 保留第一个空格后面的所有内容
                    query = content[space_index+1:].strip()
                    logger.debug(f"移除@前缀后的查询内容: {query}")
                else:
                    # 如果没有空格，尝试提取@后面的内容
                    # 找到第一个非空格字符的位置
                    for i in range(1, len(content)):
                        if content[i] != '@' and content[i] != ' ':
                            query = content[i:].strip()
                            logger.debug(f"提取@后面的内容: {query}")
                            break
                    else:
                        # 如果整个内容都是@，将query设为空
                        query = ""
        else:
            # 如果不是以@开头，则尝试移除@机器人名称
            for robot_name in self.robot_names:
                query = query.replace(f"@{robot_name}", "").strip()

        group_id = message["FromWxid"]
        user_wxid = message["SenderWxid"]

        # 聊天室功能已移除

        logger.debug(f"提取到的 query: {query}")

        if not query:
            await bot.send_at_message(message["FromWxid"], "\n请输入你的问题或指令。", [message["SenderWxid"]])
            return False

        # 检查唤醒词或触发词，在图片上传前获取对应模型
        model, processed_query, is_switch = self.get_model_from_message(query, message["SenderWxid"])
        if is_switch:
            model_name = next(name for name, config in self.models.items() if config == model)
            await bot.send_at_message(
                message["FromWxid"],
                f"\n已切换到{model_name.upper()}模型，将一直使用该模型直到下次切换。",
                [message["SenderWxid"]]
            )
            return False

        # 检查模型API密钥是否可用
        if not model.api_key:
            model_name = next((name for name, config in self.models.items() if config == model), '未知')
            logger.error(f"所选模型 '{model_name}' 的API密钥未配置")
            await bot.send_at_message(message["FromWxid"], f"\n此模型API密钥未配置，请联系管理员", [message["SenderWxid"]])
            return False

        # 检查是否有最近的图片
        files = []
        image_content = await self.get_cached_image(group_id)
        if image_content:
            try:
                logger.debug("@消息中发现最近的图片，准备上传到 Dify")
                file_id = await self.upload_file_to_dify(
                    image_content,
                    f"image_{int(time.time())}.jpg",  # 生成一个有效的文件名
                    "image/jpeg",
                    group_id,
                    model_config=model  # 传递正确的模型配置
                )
                if file_id:
                    logger.debug(f"图片上传成功，文件ID: {file_id}")
                    files = [file_id]
                else:
                    logger.error("图片上传失败")
            except Exception as e:
                logger.error(f"处理图片失败: {e}")

        if await self._check_point(bot, message, model):  # 传递正确的模型参数
            # 使用上面已经获取的模型和处理过的查询
            logger.info(f"@消息使用模型 '{next((name for name, config in self.models.items() if config == model), '未知')}' 处理请求")
            await self.dify(bot, message, processed_query, files=files, specific_model=model)
        else:
            logger.info(f"积分检查失败，无法处理@消息请求")
        return False

    @on_quote_message(priority=20)
    async def handle_quote(self, bot: WechatAPIClient, message: dict):
        """处理引用消息（最终修正版，增加Base64解码能力）"""
        if not self.enable or self.is_message_processed(message):
            return True

        user_wxid = message["SenderWxid"]
        content = message["Content"].strip()

        # --- 核心修改点开始 ---
        # 仅在群聊中检查触发条件，私聊直接通过
        is_group_chat = message.get("IsGroup", False)
        if is_group_chat:
            # 检查当前消息内容(content)是否@机器人
            is_at_in_current_content = any(f"@{name}" in content for name in self.robot_names)

            # 检查内容中是否包含唤醒词
            _, query_after_wakeup_clean, _ = self.get_model_from_message(content, user_wxid)
            wakeup_detected = content.lower() != query_after_wakeup_clean.lower()

            # 新增：检查是否以三类触发词开头
            tertiary_trigger_detected = False
            for trigger in self.tertiary_triggers:
                if content.startswith(trigger):
                    tertiary_trigger_detected = True
                    logger.info(f"群聊引用消息检测到三类触发词: '{trigger}'")
                    break # 找到一个就立即停止搜索，提高效率

            # 只有在当前消息@了机器人、包含唤醒词或以三类触发词开头时，才继续处理
            if not (is_at_in_current_content or wakeup_detected or tertiary_trigger_detected):
                logger.info("群聊引用消息未@机器人、未使用唤醒词或三类触发词，Dify插件忽略。")
                return True # 返回True表示消费此消息，但不做任何事
        # --- 核心修改点结束 ---

        self.mark_message_processed(message)
        logger.info(f"Dify插件处理引用消息，来自: {user_wxid}")

        # 获取模型，私聊时即使没有唤醒词也能正确获取默认模型
        model, query_after_wakeup_clean, _ = self.get_model_from_message(content, user_wxid)

        if not await self._check_point(bot, message, model):
            return False

        # --- 统一使用经过验证的、更稳健的@名称清理逻辑 ---
        final_query = query_after_wakeup_clean
        
        # 检查并移除@机器人名称前缀
        if final_query.startswith('@'):
            for robot_name in self.robot_names:
                prefix_to_check = f'@{robot_name}'
                if final_query.startswith(prefix_to_check):
                    # 移除前缀并清理前后空格
                    final_query = final_query[len(prefix_to_check):].strip()
                    logger.info(f"成功移除引用消息中的@前缀，清理后Query: '{final_query}'")
                    break

        quote_info = message.get("Quote", {})
        quoted_content = quote_info.get("Content", "")
        # 注意：这里的ImageMD5是当前消息的，不是引用的，所以我们主要依赖解析XML
        is_quote_image = quote_info.get("MsgType") == 3
        
        files_to_upload = []
        image_data = None

        if is_quote_image:
            logger.info("引用内容是图片，开始处理图片...")
            
            xml_root = None
            image_md5 = None # 初始化MD5变量

            # --- 核心修复逻辑开始 ---
            # 采用更鲁棒的方式解析XML，不再强制要求`<?xml`头部
            if quoted_content and "<msg>" in quoted_content:
                # 从<msg>标签开始截取，以应对缺少<?xml>头的情况
                xml_start_index = quoted_content.find("<msg>")
                if xml_start_index != -1:
                    clean_xml = quoted_content[xml_start_index:]
                    try:
                        xml_root = ET.fromstring(clean_xml)
                        img_element = xml_root.find('.//img')
                        if img_element is not None:
                            image_md5 = img_element.get('md5')
                            logger.info(f"从引用XML中成功提取MD5: {image_md5 or '空'}")
                    except ET.ParseError as e:
                        logger.error(f"解析引用XML失败: {e}")
                        xml_root = None # 解析失败，确保xml_root为None
            # --- 核心修复逻辑结束 ---
            is_already_saved = False # 标记图片是否已在本地找到

            if image_md5:
                logger.info(f"A计划：尝试根据MD5 '{image_md5}' 查找本地图片。")
                # 临时代用逻辑，实际应调用find_image_by_md5
                possible_extensions = ['.jpeg', '.jpg', '.png', '.gif', '.webp']
                for ext in possible_extensions:
                    file_path = os.path.join(self.files_dir, f"{image_md5}{ext}")
                    if os.path.exists(file_path):
                        with open(file_path, 'rb') as f:
                            image_data = f.read()
                        logger.info(f"A计划成功：在本地找到图片 {file_path}")
                        is_already_saved = True # 找到了本地已保存的图片，设置标记
                        break

            if not image_data and xml_root is not None:
                logger.warning("A计划失败或未执行，启动B计划：尝试从引用信息中重新下载图片。")
                try:
                    img_element = xml_root.find('.//img')
                    if img_element is not None:
                        aes_key = img_element.get('aeskey')
                        cdn_url = img_element.get('cdnmidimgurl')
                        
                        if aes_key and cdn_url:
                            logger.info(f"B计划：找到下载参数 aeskey: {aes_key[:10]}..., cdn_url: {cdn_url[:30]}...")
                            download_response = await bot.download_image(aes_key, cdn_url)
                            
                            if isinstance(download_response, dict):
                                logger.info(f"B计划调试：API返回字典，键: {list(download_response.keys())}。开始搜查数据...")
                                for key, value in download_response.items():
                                    if isinstance(value, bytes) and value:
                                        image_data = value
                                        logger.success(f"B计划成功：在键'{key}'中直接找到bytes数据。")
                                        break
                                    elif isinstance(value, str) and value:
                                        logger.info(f"在键'{key}'中找到字符串，尝试进行Base64解码...")
                                        try:
                                            image_data = base64.b64decode(value)
                                            logger.success(f"B计划成功：已将键'{key}'中的Base64字符串解码为图片数据。")
                                            break
                                        except Exception as e:
                                            logger.warning(f"解码键'{key}'的Base64字符串失败: {e}")
                                if not image_data:
                                    logger.error("B计划失败：API返回字典，但无法从中提取有效的图片数据。")
                            elif isinstance(download_response, bytes):
                                image_data = download_response
                                logger.success("B计划成功：API直接返回了bytes数据。")
                            else:
                                logger.error(f"B计划失败：API未能下载图片或返回未知格式: {type(download_response)}。")
                        else:
                            logger.error("B计划失败：XML中缺少aeskey或cdnmidimgurl。")
                    else:
                        logger.error("B计划失败：XML中未找到<img>标签。")
                except Exception as e:
                    logger.error(f"B计划执行下载时出错: {e}")
#
            if image_data:
                # --- 核心修复逻辑开始 ---
                # 无论图片来自何处，我们先在内存中将其转换为最终的JPEG格式，并计算其MD5
                processed_info = await self._save_image_and_get_md5(image_data)
                
                if processed_info:
                    final_md5, jpeg_content = processed_info
                    file_path = os.path.join(self.files_dir, f"{final_md5}.jpeg")
                    
                    # 检查这张处理后的图片是否已存在于本地
                    if os.path.exists(file_path):
                        logger.info(f"优化：处理后的图片 '{file_path}' 已在本地找到，无需重复下载和保存，直接上传。")
                    else:
                        # 如果不存在，则将内存中的jpeg内容写入文件
                        with open(file_path, "wb") as f:
                            f.write(jpeg_content)
                        logger.info(f"新图片已处理并保存至: {file_path}")

                    # 准备上传文件到Dify
                    file_info = await self.upload_file_to_dify(
                        jpeg_content, f"{final_md5}.jpeg", "image/jpeg", user_wxid, model_config=model
                    )
                    if file_info:
                        files_to_upload.append(file_info)
                    else:
                        logger.error("为图片准备上传信息时失败。")
                else:
                    logger.error("处理下载的图片时失败，无法继续。")
                # --- 核心修复逻辑结束 ---
            else:
                logger.error("A计划和B计划均失败，无法获取引用的图片。")
                # 在群聊中@发送者，私聊则直接发送
                reply_text = "抱歉，无法识别引用的图片信息。"
                if is_group_chat:
                    await bot.send_at_message(message["FromWxid"], f"\n{reply_text}", [user_wxid])
                else:
                    await bot.send_text_message(message["FromWxid"], reply_text)
                return False
        else:
            logger.info("引用内容是文字，合并内容作为Query。")
            final_query = f"{final_query}:{quoted_content}"
            
        logger.info(f"最终发送给Dify的Query: '{final_query[:100]}...' | 文件数: {len(files_to_upload)}")
        await self.dify(bot, message, final_query, files=files_to_upload, specific_model=model)
        return False

    @on_voice_message(priority=20)
    async def handle_voice(self, bot: WechatAPIClient, message: dict):
        if not self.enable:
            return

        if message["IsGroup"]:
            return

        if not self.current_model.api_key:
            await bot.send_text_message(message["FromWxid"], "你还没配置Dify API密钥！")
            return False

        query = await self.audio_to_text(bot, message)
        if not query:
            await bot.send_text_message(message["FromWxid"], VOICE_TRANSCRIPTION_FAILED)
            return False

        logger.debug(f"语音转文字结果: {query}")

        # 识别可能的唤醒词
        model, processed_query, is_switch = self.get_model_from_message(query, message["SenderWxid"])
        if is_switch:
            model_name = next(name for name, config in self.models.items() if config == model)
            await bot.send_text_message(
                message["FromWxid"],
                f"已切换到{model_name.upper()}模型，将一直使用该模型直到下次切换。"
            )
            return False

        # 检查识别到的模型API密钥是否可用
        if not model.api_key:
            model_name = next((name for name, config in self.models.items() if config == model), '未知')
            logger.error(f"语音消息选择的模型 '{model_name}' 的API密钥未配置")
            await bot.send_text_message(message["FromWxid"], "所选模型的API密钥未配置，请联系管理员")
            return False

        # 积分检查
        if await self._check_point(bot, message, model):
            logger.info(f"语音消息使用模型 '{next((name for name, config in self.models.items() if config == model), '未知')}' 处理请求")
            await self.dify(bot, message, processed_query, specific_model=model)
        else:
            logger.info(f"积分检查失败，无法处理语音消息请求")
        return False

    def is_at_message(self, message: dict) -> bool:
        """检查消息是否@了机器人

        支持检测普通消息和引用消息中的@
        """
        if not message["IsGroup"]:
            return False

        # 获取消息内容
        content = message["Content"]

        # 记录原始消息信息便于调试
        logger.debug(f"检查消息是否@机器人: {content[:50]}...")

        # 检查消息类型
        msg_type = message.get("MsgType")
        logger.debug(f"消息类型: {msg_type}, 是否有Quote字段: {'Quote' in message}")

        # 增强对XML引用消息的处理
        if "Quote" in message:
            logger.info(f"详细检查引用消息是否@机器人: {content[:50]}...")

            # 直接检查消息内容中是否包含@机器人
            for robot_name in self.robot_names:
                # 检查格式: "@小球子 xxx"
                if f"@{robot_name}" in content:
                    logger.info(f"在引用消息内容中发现@{robot_name}")
                    return True

                # 检查格式: "@小球子"（消息开头）
                if content.startswith(f'@{robot_name}'):
                    logger.info(f"引用消息内容以@{robot_name}开头")
                    return True

                # 特殊处理：检查是否是@小球子这样的格式（忽略大小写）
                if content.lower().startswith(f'@{robot_name.lower()}'):
                    logger.info(f"引用消息内容以@{robot_name}开头（忽略大小写）")
                    return True

                # 检查格式: "@小球子"（消息中间）
                if self.at_patterns.get(robot_name) and self.at_patterns[robot_name].search(content):
                    logger.info(f"在引用消息内容中发现@{robot_name}（正则匹配）")
                    return True

            # 检查消息内容是否以@开头，后面跟着空格和其他内容
            if content.startswith('@'):
                # 提取@后面的名称部分
                space_index = content.find(' ')
                if space_index > 0:
                    at_name = content[1:space_index].strip()
                    logger.info(f"提取到@名称: {at_name}")

                    # 检查提取的名称是否是机器人名称
                    for robot_name in self.robot_names:
                        if at_name == robot_name or at_name.lower() == robot_name.lower():
                            logger.info(f"@名称匹配机器人名称: {robot_name}")
                            return True

                        # 检查名称是否部分匹配（例如@小球 可能是@小球子的简写）
                        if robot_name.startswith(at_name) or robot_name.lower().startswith(at_name.lower()):
                            logger.info(f"@名称部分匹配机器人名称: {at_name} -> {robot_name}")
                            return True

        # 如果消息内容以@开头，这是一个强烈的信号，表明用户@了某人
        if content.startswith('@'):
            logger.debug(f"消息内容以@开头: {content[:20]}")
            # 检查@的是否是机器人
            for robot_name in self.robot_names:
                if content.startswith(f'@{robot_name}'):
                    logger.debug(f"消息内容以@{robot_name}开头")
                    return True

                # 特殊处理：检查是否是@小小x这样的格式（可能有空格）
                if content.lower().startswith(f'@{robot_name.lower()}'):
                    logger.debug(f"消息内容以@{robot_name}开头（忽略大小写）")
                    return True
            # 如果@的不是机器人，继续检查其他条件

        # 检查普通消息中的@
        for robot_name in self.robot_names:
            if f"@{robot_name}" in content:
                logger.debug(f"在消息内容中发现@{robot_name}")
                return True

        # 如果是引用消息，检查消息类型
        if msg_type == 49 or msg_type == 57 or "Quote" in message:  # 引用消息类型
            logger.debug(f"检测到引用消息: {msg_type}, Quote字段: {'Quote' in message}")

            # 特殊处理：如果消息内容以@开头，这是一个强烈的信号，表明用户@了某人
            if content.startswith('@'):
                for robot_name in self.robot_names:
                    if content.startswith(f'@{robot_name}'):
                        logger.debug(f"引用消息内容以@{robot_name}开头")
                        return True

                    # 特殊处理：检查是否是@小小x这样的格式（可能有空格）
                    if content.lower().startswith(f'@{robot_name.lower()}'):
                        logger.debug(f"引用消息内容以@{robot_name}开头（忽略大小写）")
                        return True

            # 如果有Quote字段，检查引用的消息内容
            if "Quote" in message:
                quote_info = message.get("Quote", {})
                quote_from = quote_info.get("Nickname", "")

                # 检查被引用的消息是否来自机器人 (此逻辑已停用，避免过度响应)
                # for robot_name in self.robot_names:
                #     if robot_name == quote_from:
                #         logger.debug(f"引用了机器人 '{robot_name}' 的消息")
                #         return True

                # 检查引用消息的内容中是否有@机器人
                quote_content = quote_info.get("Content", "")
                for robot_name in self.robot_names:
                    if f"@{robot_name}" in quote_content:
                        logger.debug(f"在引用的消息内容中发现@{robot_name}")
                        return True

            # 如果有OriginalContent，尝试解析XML
            if "OriginalContent" in message:
                try:
                    root = ET.fromstring(message.get("OriginalContent", ""))
                    title = root.find("appmsg/title")
                    if title is not None and title.text:
                        # 检查引用消息的标题中是否包含@机器人
                        for robot_name in self.robot_names:
                            if f"@{robot_name}" in title.text:
                                logger.debug(f"在引用消息标题中发现@{robot_name}")
                                return True
                except Exception as e:
                    logger.debug(f"解析引用消息 XML 失败: {e}")

            # 特殊处理：如果消息内容中包含机器人名称（不带@符号）
            for robot_name in self.robot_names:
                if robot_name in content:
                    logger.debug(f"在引用消息内容中发现机器人名称: {robot_name}")
                    return True

        # 检查消息的Ats字段，这是一个直接的@标记
        if "Ats" in message and message["Ats"]:
            logger.debug(f"消息包含Ats字段: {message['Ats']}")
            # 如果机器人的wxid在Ats列表中，则返回True
            # 检查所有可能的机器人wxid
            for wxid in ["wxid_uz9za1pqr3ea22", "wxid_p60yfpl5zg2m29"]:
                if wxid in message["Ats"]:
                    logger.debug(f"在Ats字段中发现机器人的wxid: {wxid}")
                    return True

        return False

    async def dify(self, bot: WechatAPIClient, message: dict, query: str, files: list = None, specific_model=None):
        """发送消息到Dify API"""
        if files is None:
            files = []

        # 如果提供了specific_model，直接使用；否则根据消息内容选择模型
        if specific_model:
            model = specific_model
            processed_query = query
            is_switch = False
            model_name = next((name for name, config in self.models.items() if config == model), '未知')
            logger.info(f"使用指定的模型 '{model_name}'")
        else:
            # 根据消息内容选择模型
            model, processed_query, is_switch = self.get_model_from_message(query, message["SenderWxid"])
            model_name = next((name for name, config in self.models.items() if config == model), '默认')
            logger.info(f"从消息内容选择模型 '{model_name}'")

            # 如果是切换模型的命令
            if is_switch:
                model_name = next(name for name, config in self.models.items() if config == model)
                await bot.send_text_message(
                    message["FromWxid"],
                    f"已切换到{model_name.upper()}模型，将一直使用该模型直到下次切换。"
                )
                return

        # 记录将要使用的模型配置
        logger.info(f"模型API密钥: {model.api_key[:5]}...{model.api_key[-5:] if len(model.api_key) > 10 else ''}")
        logger.info(f"模型API端点: {model.base_url}")

        # 处理文件上传
        formatted_files = []
        for file_info in files:
            if isinstance(file_info, dict) and "id" in file_info and "type" in file_info:
                # 新格式，已包含类型信息
                formatted_files.append({
                    "type": file_info["type"],
                    "transfer_method": "local_file",
                    "upload_file_id": file_info["id"]
                })
            else:
                # 兼容旧格式，假设是图片ID
                formatted_files.append({
                    "type": "image",
                    "transfer_method": "local_file",
                    "upload_file_id": file_info
                })
        """
        # 移除此处对通用缓存文件的检查和上传逻辑。
        # 只有在 handle_text, handle_at, handle_quote 等函数中明确判断为图片时，
        # 才会将图片文件ID添加到 files 列表中并传递给 dify 函数。
        # 这样可以避免在纯文本对话中自动上传视频等非图片文件。

        # 检查是否有缓存的文件
        cached_file = await self.get_cached_file(message["SenderWxid"])
        if cached_file:
            file_content, file_name, mime_type = cached_file
            logger.info(f"发现缓存文件，准备上传到 Dify: {file_name}, 大小: {len(file_content)} 字节")

            # 上传文件到 Dify
            file_info = await self.upload_file_to_dify(file_content, file_name, mime_type, message["SenderWxid"], model_config=model)
            if file_info:
                logger.info(f"成功上传缓存文件到 Dify，文件ID: {file_info['id']}, 类型: {file_info['type']}")
                formatted_files.append({
                    "type": file_info["type"],
                    "transfer_method": "local_file",
                    "upload_file_id": file_info["id"]
                })
        """
        try:
            logger.debug(f"开始调用 Dify API - 用户消息: {processed_query}")
            logger.debug(f"文件列表: {formatted_files}")

            # 获取会话ID
            user_wxid = message["SenderWxid"]
            from_wxid = message["FromWxid"]

            # 对于群聊消息，可以选择使用群聊ID或发送者ID作为会话ID的键
            if message["IsGroup"]:
                # 检查配置，决定使用群聊ID还是发送者ID
                # 默认使用群聊ID作为会话ID的键，这与原始行为一致
                use_group_id = True

                if use_group_id:
                    # 使用群聊ID作为会话ID的键
                    logger.debug(f"群聊消息，使用群聊ID '{from_wxid}' 获取会话ID")
                    conversation_id = self.db.get_llm_thread_id(from_wxid, namespace="dify")
                else:
                    # 使用发送者的wxid作为会话ID的键
                    logger.debug(f"群聊消息，使用发送者wxid '{user_wxid}' 获取会话ID")
                    conversation_id = self.db.get_llm_thread_id(user_wxid, namespace="dify")
            else:
                # 私聊消息，使用原来的FromWxid
                conversation_id = self.db.get_llm_thread_id(from_wxid, namespace="dify")

            try:
                user_username = await bot.get_nickname(user_wxid) or "未知用户"
            except:
                user_username = "未知用户"

            inputs = {
                "user_wxid": user_wxid,
                "user_username": user_username
            }

            # 根据是否支持Agent模式，设置不同的请求参数
            # 对于群聊消息，使用群聊ID作为user参数，这样对话会与群聊关联，而不是与个人关联
            user_id = from_wxid if message["IsGroup"] else user_wxid

            payload = {
                "inputs": inputs,
                "query": processed_query,
                "response_mode": "streaming",  # 始终使用流式响应
                "conversation_id": conversation_id,
                "user": user_id,  # 对于群聊使用群聊ID，对于私聊使用发送者的wxid
                "files": formatted_files,
                "auto_generate_name": False,
            }

            # 决定是使用API代理还是直接连接
            use_api_proxy = self.api_proxy is not None and has_api_proxy
            logger.debug(f"发送请求到 Dify - URL: {model.base_url}/chat-messages, Payload: {json.dumps(payload)}")

            if use_api_proxy:
                # 使用API代理调用
                logger.info(f"通过API代理调用Dify")
                try:
                    # 检查是否有对应的注册API
                    base_url_without_v1 = model.base_url.rstrip("/v1")
                    endpoint = model.base_url.replace(base_url_without_v1, "")
                    endpoint = endpoint + "/chat-messages"

                    # 准备请求
                    api_response = await self.api_proxy.call_api(
                        api_type="dify",
                        endpoint=endpoint,
                        data=payload,
                        method="POST",
                        headers={"Authorization": f"Bearer {model.api_key}"}
                    )

                    if api_response.get("success") is False:
                        logger.error(f"API代理调用失败: {api_response.get('error')}")
                        # 失败时回退到直接调用
                        use_api_proxy = False
                    else:
                        # API代理不支持流式响应，处理非流式返回的结果
                        ai_resp = api_response.get("data", {}).get("answer", "")
                        new_con_id = api_response.get("data", {}).get("conversation_id", "")
                        if new_con_id and new_con_id != conversation_id:
                            # 根据消息类型选择正确的ID来保存会话ID
                            if message["IsGroup"]:
                                # 群聊消息，使用群聊ID
                                self.db.save_llm_thread_id(message["FromWxid"], new_con_id, "dify")
                                logger.debug(f"群聊消息，保存会话ID到群聊ID: {message['FromWxid']}")
                            else:
                                # 私聊消息，使用原来的FromWxid
                                self.db.save_llm_thread_id(message["FromWxid"], new_con_id, "dify")

                        # 过滤掉思考标签
                        think_pattern = r'<think>.*?</think>'
                        ai_resp = re.sub(think_pattern, '', ai_resp, flags=re.DOTALL)
                        logger.debug(f"API代理返回(过滤思考标签后): {ai_resp[:100]}...")

                        if ai_resp:
                            # 获取消息ID，如果有的话
                            message_id = api_response.get("data", {}).get("message_id")
                            if message_id:
                                logger.debug(f"API代理返回消息ID: {message_id}")
                                await self.dify_handle_text(bot, message, ai_resp, model, message_id=message_id)
                            else:
                                await self.dify_handle_text(bot, message, ai_resp, model)
                        else:
                            logger.warning("API代理未返回有效响应")
                            # 回退到直接调用
                            use_api_proxy = False
                except Exception as e:
                    logger.error(f"API代理调用异常: {e}")
                    logger.error(traceback.format_exc())
                    # 出错时回退到直接调用
                    use_api_proxy = False

            # 如果API代理不可用或调用失败，使用直接连接
            if not use_api_proxy:
                headers = {"Authorization": f"Bearer {model.api_key}", "Content-Type": "application/json"}
                ai_resp = ""
                # 设置更大的缓冲区来处理大响应数据
                connector = aiohttp.TCPConnector(limit=100, limit_per_host=30)
                timeout = aiohttp.ClientTimeout(total=300)  # 5分钟超时
                async with aiohttp.ClientSession(
                    connector=connector,
                    timeout=timeout,
                    read_bufsize=2*1024*1024,  # 2MB读取缓冲区
                    max_line_size=16*1024*1024,  # 16MB最大行大小
                    max_field_size=16*1024*1024  # 16MB最大字段大小
                ) as session:
                    # 正确的方式是在请求时设置代理，而不是在创建会话时
                    proxy = self.http_proxy if self.http_proxy else None
                    async with session.post(url=f"{model.base_url}/chat-messages", headers=headers, data=json.dumps(payload), proxy=proxy) as resp:
                        if resp.status in (200, 201):
                            async for line in resp.content:
                                line = line.decode("utf-8").strip()
                                if not line or line == "event: ping":
                                    continue
                                elif line.startswith("data: "):
                                    line = line[6:]
                                try:
                                    resp_json = json.loads(line)
                                except json.JSONDecodeError:
                                    logger.error(f"Dify返回的JSON解析错误: {line}")
                                    continue

                                event = resp_json.get("event", "")
                                if event == "message":
                                    ai_resp += resp_json.get("answer", "")
                                elif event == "message_replace":
                                    ai_resp = resp_json.get("answer", "")
                                elif event == "message_end":
                                    # 在消息结束时过滤掉思考标签
                                    ai_resp = self.think_pattern.sub('', ai_resp)
                                    logger.debug(f"消息结束时过滤思考标签")
                                elif event == "message_file":
                                    file_url = resp_json.get("url", "")
                                    file_id = resp_json.get("id", "")
                                    file_type = resp_json.get("type", "image")
                                    belongs_to = resp_json.get("belongs_to", "assistant")

                                    # 存储文件信息
                                    self.agent_files[file_id] = {
                                        "url": file_url,
                                        "type": file_type,
                                        "belongs_to": belongs_to
                                    }

                                    # 处理文件
                                    if file_type == "image":
                                        #await self.dify_handle_image(bot, message, file_url, model_config=model)
                                        pass # 注释掉，交由dify_handle_text统一处理
                                    else:
                                        logger.info(f"收到非图片类型文件: {file_type}, ID: {file_id}, URL: {file_url}")
                                elif event == "agent_thought":
                                    # 处理Agent思考过程
                                    if self.support_agent_mode:
                                        thought_id = resp_json.get("id", "")
                                        message_id = resp_json.get("message_id", "")
                                        conversation_id = resp_json.get("conversation_id", "")
                                        position = resp_json.get("position", 0)
                                        thought = resp_json.get("thought", "")
                                        observation = resp_json.get("observation", "")
                                        tool = resp_json.get("tool", "")
                                        tool_input = resp_json.get("tool_input", "")
                                        message_files = resp_json.get("message_files", [])

                                        # 记录思考过程
                                        if conversation_id not in self.current_agent_thoughts:
                                            self.current_agent_thoughts[conversation_id] = []

                                        self.current_agent_thoughts[conversation_id].append({
                                            "id": thought_id,
                                            "message_id": message_id,
                                            "position": position,
                                            "thought": thought,
                                            "observation": observation,
                                            "tool": tool,
                                            "tool_input": tool_input,
                                            "files": message_files
                                        })

                                        logger.debug(f"Agent思考: {thought[:100]}...")
                                        if tool:
                                            logger.debug(f"使用工具: {tool}, 输入: {tool_input}")
                                        if observation:
                                            logger.debug(f"观察结果: {observation[:100]}...")
                                elif event == "agent_message":
                                    # 处理Agent消息
                                    if self.support_agent_mode:
                                        answer = resp_json.get("answer", "")
                                        ai_resp += answer
                                        logger.debug(f"Agent消息: {answer}")
                                elif event == "error":
                                    await self.dify_handle_error(bot, message,
                                                                resp_json.get("task_id", ""),
                                                                resp_json.get("message_id", ""),
                                                                resp_json.get("status", ""),
                                                                resp_json.get("code", ""),
                                                                resp_json.get("message", ""))

                            new_con_id = resp_json.get("conversation_id", "")
                            if new_con_id and new_con_id != conversation_id:
                                # 根据消息类型选择正确的ID来保存会话ID
                                if message["IsGroup"]:
                                    # 群聊消息，使用群聊ID
                                    self.db.save_llm_thread_id(message["FromWxid"], new_con_id, "dify")
                                    logger.debug(f"群聊消息，保存会话ID到群聊ID: {message['FromWxid']}")
                                else:
                                    # 私聊消息，使用原来的FromWxid
                                    self.db.save_llm_thread_id(message["FromWxid"], new_con_id, "dify")
                            ai_resp = ai_resp.rstrip()

                            # 最后再次过滤思考标签，确保完全移除
                            ai_resp = self.think_pattern.sub('', ai_resp)
                            logger.debug(f"Dify响应(过滤思考标签后): {ai_resp[:100]}...")
                        elif resp.status == 404:
                            logger.warning("会话ID不存在，重置会话ID并重试")
                            # 根据消息类型选择正确的ID来重置会话ID
                            if message["IsGroup"]:
                                # 群聊消息，使用群聊ID
                                self.db.save_llm_thread_id(message["FromWxid"], "", "dify")
                                logger.debug(f"群聊消息，重置会话ID，群聊ID: {message['FromWxid']}")
                            else:
                                # 私聊消息，使用原来的FromWxid
                                self.db.save_llm_thread_id(message["FromWxid"], "", "dify")
                            # 重要：在递归调用时必须传递原始模型，不要重新选择
                            return await self.dify(bot, message, processed_query, files=files, specific_model=model)
                        elif resp.status == 400:
                            # 先获取错误内容
                            error_text = await resp.content.read()
                            error_text_str = error_text.decode('utf-8')

                            logger.debug(f"收到400错误，完整错误信息: {error_text_str}")

                            # 强制重置会话ID，无论错误类型如何
                            # 这是一个更激进的解决方案，但可以确保会话ID被重置
                            logger.warning("收到400错误，强制重置会话ID")

                            # 重置会话ID
                            # 根据消息类型选择正确的ID来重置会话ID
                            if message.get("IsGroup", False):
                                # 群聊消息，使用群聊ID
                                from_wxid = message.get("FromWxid", "")
                                if from_wxid:
                                    # 确保完全清除会话ID
                                    self.db.save_llm_thread_id(from_wxid, "", "dify")
                                    logger.info(f"已重置群聊 {from_wxid} 的会话ID")
                            else:
                                # 私聊消息，使用原来的FromWxid
                                from_wxid = message.get("FromWxid", "")
                                if from_wxid:
                                    # 确保完全清除会话ID
                                    self.db.save_llm_thread_id(from_wxid, "", "dify")
                                    logger.info(f"已重置私聊用户 {from_wxid} 的会话ID")

                            # 通知用户
                            await bot.send_text_message(
                                message["FromWxid"],
                                f"{XYBOT_PREFIX}检测到对话异常，已重置对话。正在重新处理您的问题..."
                            )

                            # 等待一小段时间，确保数据库操作完成
                            await asyncio.sleep(1)

                            # 创建一个新的会话ID
                            new_conversation_id = str(uuid.uuid4())
                            logger.info(f"生成新的会话ID: {new_conversation_id}")

                            # 保存新的会话ID
                            if message.get("IsGroup", False):
                                # 群聊消息，使用群聊ID
                                self.db.save_llm_thread_id(message.get("FromWxid", ""), new_conversation_id, "dify")
                            else:
                                # 私聊消息，使用原来的FromWxid
                                self.db.save_llm_thread_id(message.get("FromWxid", ""), new_conversation_id, "dify")

                            # 修改payload，使用新的会话ID
                            payload["conversation_id"] = new_conversation_id
                            logger.info(f"更新payload中的会话ID为: {new_conversation_id}")

                            # 重新发送请求，使用新的会话ID
                            logger.info("使用新会话ID重新发送请求")

                            # 重新构建请求
                            headers = {"Authorization": f"Bearer {model.api_key}", "Content-Type": "application/json"}
                            ai_resp = ""

                            # 重新发送请求
                            logger.debug(f"重新发送请求到 Dify - URL: {model.base_url}/chat-messages, 新会话ID: {new_conversation_id}")
                            # 使用相同的配置创建新会话
                            connector = aiohttp.TCPConnector(limit=100, limit_per_host=30)
                            timeout = aiohttp.ClientTimeout(total=300)
                            async with aiohttp.ClientSession(
                                connector=connector,
                                timeout=timeout,
                                read_bufsize=2*1024*1024,  # 2MB读取缓冲区
                                max_line_size=16*1024*1024,  # 16MB最大行大小
                                max_field_size=16*1024*1024  # 16MB最大字段大小
                            ) as new_session:
                                # 正确的方式是在请求时设置代理，而不是在创建会话时
                                proxy = self.http_proxy if self.http_proxy else None
                                async with new_session.post(url=f"{model.base_url}/chat-messages", headers=headers, data=json.dumps(payload), proxy=proxy) as new_resp:
                                    if new_resp.status in (200, 201):
                                        # 处理成功响应
                                        logger.info("使用新会话ID的请求成功")
                                        # 读取响应内容
                                        async for line in new_resp.content:
                                            line = line.decode("utf-8").strip()
                                            if not line or line == "event: ping":
                                                continue
                                            elif line.startswith("data: "):
                                                line = line[6:]
                                            try:
                                                resp_json = json.loads(line)
                                                event = resp_json.get("event", "")
                                                if event == "message":
                                                    ai_resp += resp_json.get("answer", "")
                                                elif event == "message_end":
                                                    # 处理消息结束事件
                                                    think_pattern = r'<think>.*?</think>'
                                                    ai_resp = re.sub(think_pattern, '', ai_resp, flags=re.DOTALL)
                                            except json.JSONDecodeError:
                                                logger.error(f"重试请求返回的JSON解析错误: {line}")
                                                continue

                                        # 处理响应
                                        if ai_resp:
                                            await self.dify_handle_text(bot, message, ai_resp, model)
                                            return
                                        else:
                                            logger.warning("重试请求未返回有效响应")
                                    else:
                                        # 如果重试仍然失败，放弃并通知用户
                                        error_msg = await new_resp.text()
                                        logger.error(f"重试请求失败: HTTP {new_resp.status} - {error_msg}")
                                        await bot.send_text_message(
                                            message["FromWxid"],
                                            f"{XYBOT_PREFIX}重试请求失败，请稍后再试。"
                                        )
                                        return

                            # 如果执行到这里，说明重试失败，回退到原始方法
                            return await self.dify(bot, message, processed_query, files=files, specific_model=model)
                        elif resp.status == 500:
                            return await self.handle_500(bot, message)
                        else:
                            return await self.handle_other_status(bot, message, resp)

                if ai_resp:
                    # 获取消息ID，如果有的话
                    message_id = resp_json.get("message_id")
                    if message_id:
                        logger.debug(f"Dify API返回消息ID: {message_id}")
                        await self.dify_handle_text(bot, message, ai_resp, model, message_id=message_id)
                    else:
                        await self.dify_handle_text(bot, message, ai_resp, model)
                else:
                    logger.warning("Dify未返回有效响应")
        except Exception as e:
            logger.error(f"Dify API 调用失败: {e}")
            await self.handle_exceptions(bot, message, model_config=model)

    async def download_file(self, url: str) -> Optional[bytes]:
        """
        下载文件并返回文件内容（已修复SSL验证问题）
        """
        try:
            logger.info(f"开始下载文件: {url}")
            # --- 关键修复点 ---
            # 创建一个不验证SSL证书的连接器
            connector = aiohttp.TCPConnector(ssl=False)
            async with aiohttp.ClientSession(connector=connector) as session:
                proxy = self.http_proxy if self.http_proxy else None
                async with session.get(url, proxy=proxy, timeout=60) as resp:
                    if resp.status == 200:
                        content = await resp.read()
                        logger.info(f"文件下载成功，大小: {len(content)} 字节")
                        return content
                    else:
                        logger.error(f"文件下载失败: HTTP {resp.status}")
                        return None
        except Exception as e:
            logger.error(f"下载文件时发生错误: {e}")
            logger.error(traceback.format_exc())
            return None

    async def upload_file_to_dify(self, file_content: bytes, file_name: str, mime_type: str, user: str, model_config=None) -> Optional[dict]:
        """
        上传文件到Dify并返回文件信息 (已优化：使用二分查找进行图片压缩)
        返回格式: {"id": "uuid", "type": "image|document|audio|video"}
        """
        logger.info(f"开始上传文件到Dify, 用户: {user}, 文件名: {file_name}, 文件大小: {len(file_content)} 字节, MIME类型: {mime_type}")
    
        if not file_content or len(file_content) == 0:
            logger.error("文件内容为空，无法上传")
            return None
    
        try:
            file_extension = os.path.splitext(file_name)[1].lower().lstrip('.')
            if not file_extension:
                file_extension = mime_type.split('/')[-1].lower()
    
            document_extensions = ['txt', 'md', 'markdown', 'pdf', 'html', 'xlsx', 'xls', 'docx', 'csv', 'eml', 'msg', 'pptx', 'ppt', 'xml', 'epub']
            image_extensions = ['jpg', 'jpeg', 'png', 'gif', 'webp', 'svg']
            audio_extensions = ['mp3', 'm4a', 'wav', 'webm', 'amr']
            video_extensions = ['mp4', 'mov', 'mpeg', 'mpga']
    
            file_type = "custom"
            if file_extension in document_extensions or mime_type.startswith('application/') or mime_type.startswith('text/'):
                file_type = "document"
            elif file_extension in image_extensions or mime_type.startswith('image/'):
                file_type = "image"
                try:
                    from PIL import ImageFile
                    ImageFile.LOAD_TRUNCATED_IMAGES = True
                    image_io = io.BytesIO(file_content)
                    image = Image.open(image_io)
    
                    if image.mode in ('RGBA', 'LA', 'P'):
                        if image.mode == 'P':
                            image = image.convert('RGBA')
                        background = Image.new('RGB', image.size, (255, 255, 255))
                        background.paste(image, mask=image.split()[-1])
                        image = background
                    elif image.mode != 'RGB':
                        image = image.convert('RGB')
    
                    max_dimension = 1600
                    max_file_size = 1024 * 1024 * 2  # 2MB
    
                    width, height = image.size
                    if width > max_dimension or height > max_dimension:
                        ratio = min(max_dimension / width, max_dimension / height)
                        new_width = int(width * ratio)
                        new_height = int(height * ratio)
                        image = image.resize((new_width, new_height), Image.LANCZOS)
    
                    # 优化：使用二分查找来确定最佳压缩质量
                    output = io.BytesIO()
                    image.save(output, format='JPEG', quality=95, optimize=True)
                    if len(output.getvalue()) > max_file_size:
                        logger.info("图片大小超出限制，开始使用二分查找进行压缩...")
                        low, high = 10, 95
                        best_quality = -1
                        best_content = None
    
                        while low <= high:
                            quality = (low + high) // 2
                            buffer = io.BytesIO()
                            image.save(buffer, format='JPEG', quality=quality, optimize=True)
                            current_size = len(buffer.getvalue())
                            
                            if current_size <= max_file_size:
                                best_quality = quality
                                best_content = buffer.getvalue()
                                low = quality + 1 # 尝试更高的质量
                            else:
                                high = quality - 1 # 质量太高，需要降低
                        
                        if best_content:
                            file_content = best_content
                            logger.info(f"图片压缩成功，最佳质量: {best_quality}，新大小: {len(file_content)} 字节")
                        else: # 如果即使最低质量也超标，就用最低质量的结果
                            buffer = io.BytesIO()
                            image.save(buffer, format='JPEG', quality=10, optimize=True)
                            file_content = buffer.getvalue()
                            logger.warning(f"图片在最低质量下仍超标，使用质量10，大小: {len(file_content)} 字节")
                    else:
                        file_content = output.getvalue()
    
                    mime_type = 'image/jpeg'
                    file_extension = 'jpg'
    
                except Exception as e:
                    logger.error(f"图片格式转换失败: {e}", exc_info=True)
                    try:
                        Image.open(io.BytesIO(file_content))
                    except Exception as img_error:
                        logger.error(f"原始图片数据也无效: {img_error}")
                        return None
            elif file_extension in audio_extensions or mime_type.startswith('audio/'):
                file_type = "audio"
            elif file_extension in video_extensions or mime_type.startswith('video/'):
                file_type = "video"
    
            logger.info(f"文件类型判断: {file_type}, 扩展名: {file_extension}")
    
            model = model_config or self.current_model
            if not model.api_key:
                model_name = next((name for name, config in self.models.items() if config == model), '未知')
                logger.error(f"模型 '{model_name}' 的API密钥未配置，无法上传文件")
                return None
    
            processed_file_name = file_name
            if file_type == "image" and not any(processed_file_name.lower().endswith(ext) for ext in ['.jpg', '.jpeg']):
                 processed_file_name = f"{os.path.splitext(processed_file_name)[0]}.jpg"
    
            headers = {"Authorization": f"Bearer {model.api_key}"}
            formdata = aiohttp.FormData()
            formdata.add_field("file", file_content, filename=processed_file_name, content_type=mime_type)
            formdata.add_field("user", user)
    
            url = f"{model.base_url}/files/upload"
            timeout = aiohttp.ClientTimeout(total=60)
    
            try:
                async with aiohttp.ClientSession(timeout=timeout) as session:
                    proxy = self.http_proxy if self.http_proxy else None
                    async with session.post(url, headers=headers, data=formdata, proxy=proxy) as resp:
                        if resp.status in (200, 201):
                            result = await resp.json()
                            file_id = result.get("id")
                            if file_id:
                                logger.info(f"文件上传成功，文件ID: {file_id}, 类型: {file_type}")
                                if user in self.file_cache: del self.file_cache[user]
                                if file_type == "image" and user in self.image_cache: del self.image_cache[user]
                                return {"id": file_id, "type": file_type}
                            else:
                                logger.error(f"文件上传成功但未返回文件ID: {result}")
                        else:
                            error_text = await resp.text()
                            logger.error(f"文件上传失败: HTTP {resp.status} - {error_text}")
                            return None
            except aiohttp.ClientError as e:
                logger.error(f"HTTP请求失败: {e}")
                return None
        except Exception as e:
            logger.error(f"上传文件时发生错误: {e}", exc_info=True)
            return None

    async def dify_handle_text(self, bot: WechatAPIClient, message: dict, text: str, model_config=None, message_id=None):
        """
        【最终修复版】处理Dify返回的消息，恢复了//n分段发送，并保持了图片发送的修复。
        """
        # 1. 文本预处理
        text = self.think_pattern.sub('', text).strip()
        if not text:
            return
    
        # 2. 提取Markdown格式的链接和纯文本
        link_pattern = re.compile(r'!?\[.*?\]\((https?://[^\s)]+)\)')
        all_urls = link_pattern.findall(text) # 变量名改为 all_urls，表示所有链接
        text_without_links = link_pattern.sub('', text).strip()
    
        # 3. 智能分割引言和指令文本
        intro_text = ""
        instruction_text = ""
        if all_urls and '\n' in text_without_links: # 使用 all_urls
            # 如果有链接，以第一个换行符为界，分割链接前后的文字
            split_index = text_without_links.find('\n')
            intro_text = text_without_links[:split_index].strip()
            instruction_text = text_without_links[split_index:].strip()
        else:
            # 如果没有链接，所有文字都是引言
            intro_text = text_without_links
    
        # 4. 发送引言部分（使用新的分段发送函数）
        if intro_text:
            await self.send_segmented_text(bot, message, intro_text, message_id)
            # 如果后续有链接和指令，可以加个小延迟，让体验更自然
            if all_urls and instruction_text: # 使用 all_urls
                await asyncio.sleep(0.5)
    
        # 5. 处理所有链接（区分图片和视频/其他文件）
        if all_urls:
            to_wxid = message["FromWxid"]
            
            # 分离图片链接和其他文件链接
            image_urls = []
            other_file_urls = []
            for url in all_urls:
                file_type = self._get_file_type_from_url(url) # 使用新的辅助函数判断类型
                if file_type == "image":
                    image_urls.append(url)
                else:
                    other_file_urls.append(url)
            
            # 处理图片
            if image_urls:
                if len(image_urls) > 1 and self.combine_multiple_images:
                    logger.info(f"检测到 {len(image_urls)} 张图片，根据配置【执行合并】。")
                    loop = asyncio.get_event_loop()
                    combined_image_buffer, save_path = await loop.run_in_executor(None, self.processor.combine_images, image_urls)
                    
                    if combined_image_buffer:
                        image_bytes = combined_image_buffer.getvalue()
                        if image_bytes:
                            logger.info(f"合成图片成功，将通过【内存数据】直接发送，大小: {len(image_bytes)}字节")
                            await bot.send_image_message(to_wxid, image_bytes)
                        else:
                            combined_image_buffer = None # 标记失败，以便触发后备方案
                    
                    if not combined_image_buffer:
                        if save_path and os.path.exists(save_path):
                            logger.warning("内存发送失败，回退到使用文件路径发送。")
                            await bot.send_image_message(to_wxid, save_path)
                        else:
                            logger.error("图片合并失败且所有后备方案均无效，将尝试逐张发送。")
                            for url in image_urls:
                                await self.dify_handle_image(bot, message, url)
                                await asyncio.sleep(1)
                else:
                    logger.info(f"检测到 {len(image_urls)} 张图片，将【逐张发送】。")
                    for url in image_urls:
                        await self.dify_handle_image(bot, message, url)
                        if len(image_urls) > 1:
                            await asyncio.sleep(1)
            
            # 处理其他文件（视频、音频、文档等）
            if other_file_urls:
                logger.info(f"检测到 {len(other_file_urls)} 个非图片文件，将【逐个下载并发送】。")
                for url in other_file_urls:
                    await self.download_and_send_file(bot, message, url) # 调用已有的文件下载和发送函数
                    await asyncio.sleep(1) # 在发送文件之间添加小延迟
    
        # 6. 发送指令部分（同样使用新的分段发送函数）
        if instruction_text:
            # 指令部分通常不转语音，所以直接调用，但我们的辅助函数内部已包含此逻辑
            await self.send_segmented_text(bot, message, instruction_text, message_id)

    async def dify_handle_image(self, bot: WechatAPIClient, message: dict, image_url: str, model_config=None):
        """
        【核心修改】处理Dify返回的单个图片URL，直接从内存发送数据，并忽略SSL错误。
        """
        try:
            logger.info(f"准备处理图片URL: {image_url}")
            image_content = None
            
            # --- 智能下载逻辑 ---
            use_playwright = has_playwright_downloader and any(domain in image_url for domain in ["byteimg.com", "dreamina.cn", "doubao"])
            
            if use_playwright:
                logger.info("检测到特殊URL，尝试使用Playwright下载...")
                async with self.playwright_semaphore:
                    image_content = await download_with_playwright(image_url)
            
            if not image_content:
                if use_playwright:
                    logger.warning("Playwright下载失败，回退到标准HTTP下载...")
                
                logger.info("使用标准HTTP下载器。")
                # --- 关键修复点 ---
                # 创建一个不验证SSL证书的连接器
                connector = aiohttp.TCPConnector(ssl=False)
                async with aiohttp.ClientSession(connector=connector) as session:
                    proxy = self.http_proxy if self.http_proxy and self.http_proxy.strip() else None
                    try:
                        async with session.get(image_url, proxy=proxy, timeout=60) as resp:
                            if resp.status == 200:
                                image_content = await resp.read()
                            else:
                                logger.error(f"标准下载失败: HTTP {resp.status} for {image_url}")
                    except aiohttp.ClientConnectorError as e:
                        logger.error(f"标准下载时连接错误: {e}")
                        # 即使有连接错误，也继续尝试，因为可能已经被上层捕获处理
            
            if not image_content:
                logger.error(f"所有下载方法均失败，无法获取图片: {image_url}")
                await bot.send_text_message(message["FromWxid"], f"图片下载失败:\n{image_url}")
                return
    
            # --- 统一保存和发送逻辑 ---
            result = await self._save_image_and_get_md5(image_content)
            if result:
                _ , jpeg_content = result
                
                if jpeg_content:
                    logger.info(f"图片下载并统一处理成功，将通过【内存数据】直接发送，大小: {len(jpeg_content)}字节")
                    await bot.send_image_message(message["FromWxid"], jpeg_content)
                else:
                    logger.error(f"图片处理后内容为空，无法发送: {image_url}")
            else:
                logger.error(f"下载图片后，保存或处理失败: {image_url}")
    
        except Exception as e:
            logger.error(f"处理图片URL时发生严重错误: {e}")
            logger.error(traceback.format_exc())
            # 避免因为 aiohttp 的 ClientConnectorCertificateError 重复发送错误信息
            if not isinstance(e, aiohttp.ClientConnectorCertificateError):
                await bot.send_text_message(message["FromWxid"], f"处理图片失败: {str(e)}")

    @staticmethod
    async def dify_handle_error(bot: WechatAPIClient, message: dict, task_id: str, message_id: str, status: str,
                                code: int, err_message: str):
        output = (XYBOT_PREFIX +
                  DIFY_ERROR_MESSAGE +
                  f"任务 ID：{task_id}\n"
                  f"消息唯一 ID：{message_id}\n"
                  f"HTTP 状态码：{status}\n"
                  f"错误码：{code}\n"
                  f"错误信息：{err_message}")
        await bot.send_text_message(message["FromWxid"], output)



    @staticmethod
    async def handle_500(bot: WechatAPIClient, message: dict):
        output = XYBOT_PREFIX + "🙅对不起，Dify服务内部异常，请稍后再试。"
        await bot.send_text_message(message["FromWxid"], output)

    @staticmethod
    async def handle_other_status(bot: WechatAPIClient, message: dict, resp: aiohttp.ClientResponse):
        ai_resp = (XYBOT_PREFIX +
                   f"🙅对不起，出现错误！\n"
                   f"状态码：{resp.status}\n"
                   f"错误信息：{(await resp.content.read()).decode('utf-8')}")
        await bot.send_text_message(message["FromWxid"], ai_resp)

    @staticmethod
    async def handle_exceptions(bot: WechatAPIClient, message: dict, model_config=None):
        output = (XYBOT_PREFIX +
                  "🙅对不起，出现错误！\n"
                  f"错误信息：\n"
                  f"{traceback.format_exc()}")
        await bot.send_text_message(message["FromWxid"], output)

    async def _check_point(self, bot: WechatAPIClient, message: dict, model_config=None) -> bool:
        wxid = message["SenderWxid"]
        if wxid in self.admins and self.admin_ignore:
            return True
        elif self.db.get_whitelist(wxid) and self.whitelist_ignore:
            return True
        else:
            if self.db.get_points(wxid) < (model_config or self.current_model).price:
                await bot.send_text_message(message["FromWxid"],
                                            XYBOT_PREFIX +
                                            INSUFFICIENT_POINTS_MESSAGE.format(price=(model_config or self.current_model).price))
                return False
            self.db.add_points(wxid, -((model_config or self.current_model).price))
            return True

    async def audio_to_text(self, bot: WechatAPIClient, message: dict) -> str:
        if not shutil.which("ffmpeg"):
            logger.error("未找到ffmpeg，请安装并配置到环境变量")
            await bot.send_text_message(message["FromWxid"], "服务器缺少ffmpeg，无法处理语音")
            return ""

        silk_file = "temp_audio.silk"
        mp3_file = "temp_audio.mp3"
        try:
            with open(silk_file, "wb") as f:
                f.write(message["Content"])

            command = f"ffmpeg -y -i {silk_file} -ar 16000 -ac 1 -f mp3 {mp3_file}"
            process = subprocess.run(command, shell=True, check=True, capture_output=True, text=True)
            if process.returncode != 0:
                logger.error(f"ffmpeg 执行失败: {process.stderr}")
                return ""

            # 使用当前模型的 base-url 构建音频转文本 URL
            model = self.get_user_model(message["SenderWxid"])
            audio_to_text_url = f"{model.base_url}/audio-to-text"
            logger.debug(f"使用音频转文本 URL: {audio_to_text_url}")

            headers = {"Authorization": f"Bearer {model.api_key}"}
            formdata = aiohttp.FormData()
            with open(mp3_file, "rb") as f:
                mp3_data = f.read()
            formdata.add_field("file", mp3_data, filename="audio.mp3", content_type="audio/mp3")
            # 对于群聊消息，使用群聊ID作为user参数，这样对话会与群聊关联，而不是与个人关联
            user_id = message["FromWxid"] if message.get("IsGroup", False) else message["SenderWxid"]
            formdata.add_field("user", user_id)
            async with aiohttp.ClientSession() as session:
                # 正确的方式是在请求时设置代理，而不是在创建会话时
                proxy = self.http_proxy if self.http_proxy and self.http_proxy.strip() else None
                async with session.post(audio_to_text_url, headers=headers, data=formdata, proxy=proxy) as resp:
                    if resp.status == 200:
                        result = await resp.json()
                        text = result.get("text", "")
                        if "failed" in text.lower() or "code" in text.lower():
                            logger.error(f"Dify API 返回错误: {text}")
                        else:
                            logger.info(f"语音转文字结果 (Dify API): {text}")
                            return text
                    else:
                        logger.error(f"audio-to-text 接口调用失败: {resp.status} - {await resp.text()})")

            command = f"ffmpeg -y -i {mp3_file} {silk_file.replace('.silk', '.wav')}"
            process = subprocess.run(command, shell=True, check=True, capture_output=True, text=True)
            if process.returncode != 0:
                logger.error(f"ffmpeg 转为 WAV 失败: {process.stderr}")
                return ""

            r = sr.Recognizer()
            with sr.AudioFile(silk_file.replace('.silk', '.wav')) as source:
                audio = r.record(source)
            text = r.recognize_google(audio, language="zh-CN")
            logger.info(f"语音转文字结果 (Google): {text}")
            return text
        except Exception as e:
            logger.error(f"语音处理失败: {e}")
            return ""
        finally:
            for temp_file in [silk_file, mp3_file, silk_file.replace('.silk', '.wav')]:
                if os.path.exists(temp_file):
                    os.remove(temp_file)

    async def text_to_voice_message(self, bot: WechatAPIClient, message: dict, text: str = None, message_id: str = None):
        """
        将文本转换为语音消息并发送

        Args:
            bot: WechatAPIClient实例
            message: 消息字典
            text: 要转换为语音的文本内容（可选，如果提供message_id则可为None）
            message_id: Dify生成的消息ID（可选，优先级高于text）
        """
        try:
            # 使用当前模型的 base-url 构建文本转音频 URL
            model = self.get_user_model(message["SenderWxid"])
            text_to_audio_url = f"{model.base_url}/text-to-audio"
            logger.debug(f"使用文本转音频 URL: {text_to_audio_url}")

            headers = {"Authorization": f"Bearer {model.api_key}", "Content-Type": "application/json"}

            # 构建请求数据，支持message_id参数
            data = {"user": message["SenderWxid"]}

            # 优先使用message_id，如果没有则使用text
            if message_id:
                data["message_id"] = message_id
                logger.debug(f"使用message_id: {message_id}进行文本转语音")
            elif text:
                data["text"] = text
                logger.debug(f"使用text进行文本转语音: {text[:50]}..." if len(text) > 50 else f"使用text进行文本转语音: {text}")
            else:
                logger.error("文本转语音失败: 未提供text或message_id参数")
                await bot.send_text_message(message["FromWxid"], f"{TEXT_TO_VOICE_FAILED}: 未提供文本内容或消息ID")
                return

            async with aiohttp.ClientSession(proxy=self.http_proxy) as session:
                async with session.post(text_to_audio_url, headers=headers, json=data) as resp:
                    if resp.status == 200:
                        audio = await resp.read()
                        await bot.send_voice_message(message["FromWxid"], voice=audio, format="mp3")
                        logger.info(f"文本转语音成功，{'使用message_id' if message_id else '使用text'}")
                    else:
                        error_text = await resp.text()
                        logger.error(f"text-to-audio 接口调用失败: {resp.status} - {error_text}")
                        await bot.send_text_message(message["FromWxid"], f"{TEXT_TO_VOICE_FAILED}: 状态码 {resp.status}")
        except Exception as e:
            logger.error(f"text-to-audio 接口调用异常: {e}")
            logger.error(traceback.format_exc())
            await bot.send_text_message(message["FromWxid"], f"{TEXT_TO_VOICE_FAILED}: {str(e)}")

    @on_image_message(priority=20)
    async def handle_image(self, bot: WechatAPIClient, message: dict):
        """处理用户发送的图片消息（优化版：仅缓存，不重复保存）"""
        if not self.enable:
            return

        try:
            from_wxid = message.get("FromWxid")
            sender_wxid = message.get("SenderWxid")
            logger.info(f"收到来自 {sender_wxid} 的图片消息，准备缓存。")

            image_content = message.get("Content")
            final_image_bytes = None

            # 智能判断内容类型
            if isinstance(image_content, bytes):
                # 理想情况：内容已经是二进制数据
                logger.info("图片内容已是bytes格式，直接使用。")
                final_image_bytes = image_content
            elif isinstance(image_content, str):
                # 内容是字符串，需要区分是XML还是Base64
                if image_content.strip().startswith("<?xml"):
                    # 情况1：内容是XML，需要我们自己下载
                    logger.info("内容是XML字符串，通过API下载图片。")
                    final_image_bytes = await bot.get_msg_image(image_content, from_wxid)
                else:
                    # 情况2：内容是字符串但不是XML，极有可能是框架预处理后的Base64
                    logger.info("内容是字符串但非XML，尝试作为Base64解码。")
                    try:
                        final_image_bytes = base64.b64decode(image_content)
                    except Exception as e:
                        logger.error(f"Base64解码失败: {e}。无法处理该图片。")
                        final_image_bytes = None
            else:
                logger.error(f"未知的图片内容类型: {type(image_content)}，无法处理。")

            # 仅当成功获取图片二进制数据时，才进行缓存
            if final_image_bytes:
                # 缓存原始图片内容以备立即引用
                self.image_cache[sender_wxid] = {
                    "content": final_image_bytes,
                    "timestamp": time.time()
                }
                # 如果是群聊，也以群ID为键缓存一份
                if from_wxid != sender_wxid:
                    self.image_cache[from_wxid] = {
                        "content": final_image_bytes,
                        "timestamp": time.time()
                    }
                logger.info(f"图片已成功缓存，可供 {sender_wxid} 和 {from_wxid} 立即引用。")
            else:
                logger.error("未能获取图片内容，无法缓存。")

        except Exception as e:
            logger.error(f"处理图片消息时发生严重错误: {e}")
            logger.error(f"错误详情: {traceback.format_exc()}")

    async def get_cached_image(self, user_wxid: str) -> Optional[bytes]:
        """获取用户最近的图片"""
        logger.debug(f"尝试获取用户 {user_wxid} 的缓存图片")
        if user_wxid in self.image_cache:
            cache_data = self.image_cache[user_wxid]
            current_time = time.time()
            cache_age = current_time - cache_data["timestamp"]
            logger.debug(f"找到缓存图片，年龄: {cache_age:.2f}秒, 超时时间: {self.image_cache_timeout}秒")

            if cache_age <= self.image_cache_timeout:
                try:
                    # 确保我们有有效的二进制数据
                    image_content = cache_data["content"]
                    if not isinstance(image_content, bytes):
                        logger.error("缓存的图片内容不是二进制格式")
                        del self.image_cache[user_wxid]
                        return None

                    # 尝试验证图片数据
                    try:
                        img = Image.open(io.BytesIO(image_content))
                        logger.debug(f"缓存图片验证成功，格式: {img.format}, 大小: {len(image_content)} 字节")
                    except Exception as e:
                        logger.error(f"缓存的图片数据无效: {e}")
                        del self.image_cache[user_wxid]
                        return None

                    # 不再删除缓存，而是在上传成功后删除
                    # 更新时间戳，避免过早超时
                    self.image_cache[user_wxid]["timestamp"] = current_time
                    logger.info(f"成功获取用户 {user_wxid} 的缓存图片")
                    return image_content
                except Exception as e:
                    logger.error(f"处理缓存图片失败: {e}")
                    del self.image_cache[user_wxid]
                    return None
            else:
                # 超时清除
                logger.debug(f"缓存图片超时，已清除")
                del self.image_cache[user_wxid]
        else:
            logger.debug(f"未找到用户 {user_wxid} 的缓存图片")
        return None

    async def find_image_by_md5(self, md5: str) -> Optional[bytes]:
        """根据MD5查找图片文件"""
        if not md5:
            logger.warning("MD5为空，无法查找图片")
            return None

        # 检查files目录是否存在
        files_dir = os.path.join(os.getcwd(), "files")
        if not os.path.exists(files_dir):
            logger.warning(f"files目录不存在: {files_dir}")
            return None

        # 尝试查找不同扩展名的图片文件
        for ext in ['jpg', 'jpeg', 'png', 'gif', 'webp']:
            file_path = os.path.join(files_dir, f"{md5}.{ext}")
            if os.path.exists(file_path):
                try:
                    # 读取图片文件
                    with open(file_path, "rb") as f:
                        image_data = f.read()
                    logger.info(f"根据MD5找到图片文件: {file_path}, 大小: {len(image_data)} 字节")
                    return image_data
                except Exception as e:
                    logger.error(f"读取图片文件失败: {e}")

        logger.warning(f"未找到MD5为 {md5} 的图片文件")
        return None

    async def get_cached_file(self, user_wxid: str) -> Optional[tuple[bytes, str, str]]:
        """获取用户最近的文件，返回 (文件内容, 文件名, MIME类型)"""
        logger.debug(f"尝试获取用户 {user_wxid} 的缓存文件")
        if user_wxid in self.file_cache:
            cache_data = self.file_cache[user_wxid]
            current_time = time.time()
            cache_age = current_time - cache_data["timestamp"]
            logger.debug(f"找到缓存文件，年龄: {cache_age:.2f}秒, 超时时间: {self.file_cache_timeout}秒")

            if cache_age <= self.file_cache_timeout:
                try:
                    # 确保我们有有效的二进制数据
                    file_content = cache_data["content"]
                    file_name = cache_data["name"]
                    mime_type = cache_data["mime_type"]

                    # 处理不同类型的文件内容
                    if isinstance(file_content, bytearray):
                        # 将 bytearray 转换为 bytes
                        file_content = bytes(file_content)
                        logger.info(f"将 bytearray 转换为 bytes，大小: {len(file_content)} 字节")
                    elif isinstance(file_content, str):
                        # 尝试将字符串解析为 base64
                        try:
                            file_content = base64.b64decode(file_content)
                            logger.info(f"将 base64 字符串转换为 bytes，大小: {len(file_content)} 字节")
                        except Exception as e:
                            logger.error(f"Base64 解码失败: {e}")
                            file_content = file_content.encode('utf-8')
                            logger.info(f"将普通字符串转换为 bytes，大小: {len(file_content)} 字节")
                    elif not isinstance(file_content, bytes):
                        logger.error(f"缓存的文件内容不是支持的格式: {type(file_content)}")
                        del self.file_cache[user_wxid]
                        return None

                    # 更新缓存中的文件内容
                    self.file_cache[user_wxid]["content"] = file_content

                    # 更新时间戳，避免过早超时
                    self.file_cache[user_wxid]["timestamp"] = current_time
                    logger.info(f"成功获取用户 {user_wxid} 的缓存文件: {file_name}, 大小: {len(file_content)} 字节")
                    return (file_content, file_name, mime_type)
                except Exception as e:
                    logger.error(f"处理缓存文件失败: {e}")
                    del self.file_cache[user_wxid]
                    return None
            else:
                # 超时清除
                logger.debug(f"缓存文件超时，已清除")
                del self.file_cache[user_wxid]
        else:
            logger.debug(f"未找到用户 {user_wxid} 的缓存文件")
        return None

    def cache_file(self, user_wxid: str, file_content: bytes, file_name: str, mime_type: str) -> None:
        """缓存用户文件"""
        self.file_cache[user_wxid] = {
            "content": file_content,
            "name": file_name,
            "mime_type": mime_type,
            "timestamp": time.time()
        }
        logger.info(f"已缓存用户 {user_wxid} 的文件: {file_name}, 大小: {len(file_content)} 字节")

    async def download_and_send_file(self, bot: WechatAPIClient, message: dict, url: str):
        """下载并发送文件"""
        try:
            # 从URL中获取文件名
            parsed_url = urllib.parse.urlparse(url)
            filename = os.path.basename(parsed_url.path)
            if not filename:
                filename = f"downloaded_file_{int(time.time())}"

            logger.info(f"开始下载文件: {url}")

            # 使用改进后的download_file方法
            content = await self.download_file(url)
            if not content:
                await bot.send_text_message(message["FromWxid"], f"下载文件失败: {url}")
                return

            # 检测文件类型
            kind = filetype.guess(content)
            if kind is None:
                # 如果无法检测文件类型,尝试从URL获取
                ext = os.path.splitext(filename)[1].lower()
                if not ext:
                    # 如果没有扩展名，使用默认扩展名
                    ext = ".txt"
                    logger.warning(f"无法识别文件类型，使用默认扩展名: {ext}")
            else:
                ext = f".{kind.extension}"
                logger.info(f"检测到文件类型: {kind.mime}, 扩展名: {ext}")

            # 确保文件名有扩展名
            if not os.path.splitext(filename)[1]:
                filename = f"{filename}{ext}"

            # 根据文件类型发送不同类型的消息
            if ext.lower() in ['.jpg', '.jpeg', '.png', '.gif', '.bmp', '.webp', '.svg']:
                await bot.send_image_message(message["FromWxid"], content)
                logger.info(f"发送图片消息成功，文件名: {filename}, 大小: {len(content)} 字节")
            elif ext.lower() in ['.mp3', '.wav', '.ogg', '.m4a']:
                await bot.send_voice_message(message["FromWxid"], voice=content, format=ext[1:])
                logger.info(f"发送语音消息成功，文件名: {filename}, 大小: {len(content)} 字节")
            elif ext.lower() in ['.mp4', '.avi', '.mov', '.mkv', '.flv']:
                # --- 视频封面生成逻辑开始 ---
                thumbnail_bytes = None
                temp_video_path = None
                temp_thumbnail_path = None

                try:
                    # 检查ffmpeg是否可用
                    if not shutil.which("ffmpeg"):
                        logger.warning("未找到ffmpeg，无法生成视频封面。请安装ffmpeg并配置到环境变量。")
                    else:
                        # 将视频内容保存到临时文件
                        temp_video_path = os.path.join(self.files_dir, f"temp_video_{uuid.uuid4()}.{ext}")
                        with open(temp_video_path, "wb") as f:
                            f.write(content)

                        # 定义临时封面图路径
                        temp_thumbnail_path = os.path.join(self.files_dir, f"temp_thumbnail_{uuid.uuid4()}.jpg")

                        # 使用ffmpeg提取视频的第一帧作为封面，并强制调整为16:9比例（640x360）
                        # -ss 00:00:00.1: 从视频的0.1秒开始提取，应对极短视频
                        # -vframes 1: 只提取1帧
                        # -vf "scale='min(640,iw*360/ih):min(360,ih*640/iw)',pad=640:360:(ow-iw)/2:(oh-ih)/2:color=black":
                        #   - scale: 缩放图片以适应640x360的框，同时保持原始宽高比。
                        #   - pad: 在缩放后的图片周围添加黑边，使其最终尺寸为640x360，并居中。
                        # -q:v 2: 视频质量（1-31，1最高，31最低），这里设置为2，保证质量
                        command = [
                            "ffmpeg", "-y", "-i", temp_video_path,
                            "-ss", "00:00:00.1", # 从视频的0.1秒开始提取，应对极短视频
                            "-vframes", "1",
                            "-vf", "scale='min(360,iw*640/ih):min(640,ih*360/iw)',pad=360:640:(ow-iw)/2:(oh-ih)/2:color=black",
                            "-q:v", "2", # 质量设置
                            temp_thumbnail_path
                        ]

                        logger.info(f"尝试使用ffmpeg生成视频封面: {' '.join(command)}")
                        # 在单独的线程中运行ffmpeg，避免阻塞主事件循环
                        process = await asyncio.to_thread(subprocess.run, command, check=False, capture_output=True)

                        if process.returncode == 0 and os.path.exists(temp_thumbnail_path):
                            with open(temp_thumbnail_path, "rb") as f:
                                raw_thumbnail_content = f.read()

                            # 使用_save_image_and_get_md5处理封面图（压缩、格式统一）
                            processed_thumbnail_info = await self._save_image_and_get_md5(raw_thumbnail_content)
                            if processed_thumbnail_info:
                                _, thumbnail_bytes = processed_thumbnail_info
                                logger.info(f"视频封面图生成并处理成功，大小: {len(thumbnail_bytes)} 字节")
                            else:
                                logger.warning("视频封面图处理失败，将尝试发送无封面视频。")
                        else:
                            logger.warning(f"ffmpeg 提取视频封面失败。错误输出: {process.stderr.decode('utf-8', errors='ignore')}")

                except Exception as e:
                    logger.error(f"生成视频封面时发生错误: {e}")
                    logger.error(traceback.format_exc())
                finally:
                    # 清理临时文件
                    if temp_video_path and os.path.exists(temp_video_path):
                        os.remove(temp_video_path)
                        logger.debug(f"已删除临时视频文件: {temp_video_path}")
                    if temp_thumbnail_path and os.path.exists(temp_thumbnail_path):
                        os.remove(temp_thumbnail_path)
                        logger.debug(f"已删除临时封面文件: {temp_thumbnail_path}")
                # --- 视频封面生成逻辑结束 ---

                # 发送视频消息，将生成的封面图传递给image参数
                await bot.send_video_message(message["FromWxid"], video=content, image=thumbnail_bytes)
                logger.info(f"发送视频消息成功，文件名: {filename}, 大小: {len(content)} 字节，{'带封面' if thumbnail_bytes else '无封面'}")
            else:
                # 其他类型文件，发送文件信息
                await bot.send_text_message(message["FromWxid"], f"文件名: {filename}\n类型: {ext[1:]}\n大小: {len(content)/1024:.2f} KB")
                logger.info(f"发送文件信息成功，文件名: {filename}, 大小: {len(content)} 字节")

            # 缓存文件，便于后续使用
            mime_type = kind.mime if kind else f"application/{ext[1:]}"
            self.cache_file(message["SenderWxid"], content, filename, mime_type)
            logger.info(f"文件已缓存，用户: {message['SenderWxid']}, 文件名: {filename}")

            # 如果是私聊，也缓存到聊天对象的ID
            if message["FromWxid"] != message.get("SenderWxid", message["FromWxid"]):
                self.cache_file(message["FromWxid"], content, filename, mime_type)
                logger.info(f"文件已缓存到聊天对象: {message['FromWxid']}, 文件名: {filename}")

        except Exception as e:
            logger.error(f"下载或发送文件失败: {e}")
            logger.error(traceback.format_exc())

    @on_xml_message(priority=20)  # 使用高优先级确保先处理
    async def handle_xml_file(self, bot: WechatAPIClient, message: dict):
        """处理XML格式的文件消息"""
        if not self.enable:
            return True

        try:
            # 检查消息内容是否是XML格式
            content = message.get("Content", "")
            if not content or not isinstance(content, str) or not content.strip().startswith("<"):
                logger.warning(f"Dify: 消息内容不是XML格式: {content[:100]}")
                return True

            # 解析XML内容
            root = ET.fromstring(message["Content"])
            appmsg = root.find("appmsg")
            if appmsg is None:
                return True

            type_element = appmsg.find("type")
            if type_element is None:
                return True

            type_value = int(type_element.text)
            logger.info(f"Dify: XML消息类型: {type_value}")

            # 检测是否是文件消息（类型6）
            if type_value == 6:
                logger.info("Dify: 检测到文件消息")

                # 提取文件信息
                title = appmsg.find("title").text
                appattach = appmsg.find("appattach")
                attach_id = appattach.find("attachid").text
                file_extend = appattach.find("fileext").text
                total_len = int(appattach.find("totallen").text)

                logger.info(f"Dify: 文件名: {title}")
                logger.info(f"Dify: 文件扩展名: {file_extend}")
                logger.info(f"Dify: 附件ID: {attach_id}")
                logger.info(f"Dify: 文件大小: {total_len}")

                # 不发送下载提示
                logger.info(f"开始下载文件: {title}, 大小: {total_len} 字节")

                # 使用 /Tools/DownloadFile API 下载文件
                logger.info("Dify: 开始下载文件...")
                # 分段下载大文件
                # 每次下载 64KB
                chunk_size = 64 * 1024  # 64KB
                app_id = appmsg.get("appid", "")

                # 创建一个字节数组来存储完整的文件数据
                file_data = bytearray()

                # 计算需要下载的分段数量
                chunks = (total_len + chunk_size - 1) // chunk_size  # 向上取整

                logger.info(f"Dify: 开始分段下载文件，总大小: {total_len} 字节，分 {chunks} 段下载")

                # 尝试两个不同的API端点
                config_manager = ConfigManager()
                app_config = config_manager.config
                api_host = app_config.wechat_api.host
                api_port = app_config.wechat_api.port
                urls = [
                    f'http://{api_host}:{api_port}/api/Tools/DownloadFile',
                    f'http://{api_host}:{api_port}/VXAPI/Tools/DownloadFile'
                ]

                download_success = False

                for url in urls:
                    if download_success:
                        break

                    file_data.clear()  # 清空之前的数据
                    logger.info(f"Dify: 尝试使用 {url} 下载文件")

                    # 分段下载
                    for i in range(chunks):
                        start_pos = i * chunk_size
                        # 最后一段可能不足 chunk_size
                        current_chunk_size = min(chunk_size, total_len - start_pos)

                        logger.info(f"Dify: 下载第 {i+1}/{chunks} 段，起始位置: {start_pos}，大小: {current_chunk_size} 字节")

                        async with aiohttp.ClientSession() as session:
                            # 设置较长的超时时间
                            timeout = aiohttp.ClientTimeout(total=60)  # 1分钟

                            # 构造请求参数
                            json_param = {
                                "AppID": app_id,
                                "AttachId": attach_id,
                                "DataLen": total_len,
                                "Section": {
                                    "DataLen": current_chunk_size,
                                    "StartPos": start_pos
                                },
                                "UserName": "",  # 可选参数
                                "Wxid": bot.wxid
                            }

                            logger.info(f"Dify: 调用下载文件API: AttachId={attach_id}, 起始位置: {start_pos}, 大小: {current_chunk_size}")
                            response = await session.post(
                                url,
                                json=json_param,
                                timeout=timeout
                            )

                            # 处理响应
                            try:
                                json_resp = await response.json()

                                if json_resp.get("Success"):
                                    data = json_resp.get("Data")

                                    # 尝试从不同的响应格式中获取文件数据
                                    chunk_data = None
                                    if isinstance(data, dict):
                                        if "buffer" in data:
                                            chunk_data = base64.b64decode(data["buffer"])
                                        elif "data" in data and isinstance(data["data"], dict) and "buffer" in data["data"]:
                                            chunk_data = base64.b64decode(data["data"]["buffer"])
                                        else:
                                            try:
                                                chunk_data = base64.b64decode(str(data))
                                            except:
                                                logger.error(f"Dify: 无法解析文件数据: {data}")
                                    elif isinstance(data, str):
                                        try:
                                            chunk_data = base64.b64decode(data)
                                        except:
                                            logger.error(f"Dify: 无法解析文件数据字符串")

                                    if chunk_data:
                                        # 将分段数据添加到完整文件中
                                        file_data.extend(chunk_data)
                                        logger.info(f"Dify: 第 {i+1}/{chunks} 段下载成功，大小: {len(chunk_data)} 字节")
                                    else:
                                        logger.warning(f"Dify: 第 {i+1}/{chunks} 段数据为空")
                                        break
                                else:
                                    error_msg = json_resp.get("Message", "Unknown error")
                                    logger.error(f"Dify: 第 {i+1}/{chunks} 段下载失败: {error_msg}")
                                    break
                            except Exception as e:
                                logger.error(f"Dify: 解析第 {i+1}/{chunks} 段响应失败: {e}")
                                break

                    # 检查文件是否下载完整
                    if len(file_data) > 0:
                        logger.info(f"Dify: 文件下载成功: AttachId={attach_id}, 实际大小: {len(file_data)} 字节")
                        download_success = True
                        break
                    else:
                        logger.warning("Dify: 文件数据为空，尝试下一个API端点")

                # 如果文件下载成功
                if download_success:
                    # 确定文件类型
                    mime_type = mimetypes.guess_type(f"{title}.{file_extend}")[0] or "application/octet-stream"

                    # 确保文件数据是二进制格式
                    if isinstance(file_data, str):
                        try:
                            binary_file_data = base64.b64decode(file_data)
                            logger.info(f"Dify: 将base64字符串转换为二进制数据，大小: {len(binary_file_data)} 字节")
                        except Exception as e:
                            logger.error(f"Dify: Base64解码失败: {e}")
                            binary_file_data = file_data.encode('utf-8')
                    elif isinstance(file_data, bytearray):
                        binary_file_data = bytes(file_data)
                        logger.info(f"Dify: 将bytearray转换为二进制数据，大小: {len(binary_file_data)} 字节")
                    else:
                        binary_file_data = file_data

                    # 处理文件名，避免重复的扩展名
                    if title.lower().endswith(f".{file_extend.lower()}"):
                        file_name = title  # 如果标题已经包含扩展名，直接使用
                    else:
                        file_name = f"{title}.{file_extend}"  # 否则添加扩展名

                    logger.info(f"Dify: 处理后的文件名: {file_name}")

                    # 缓存文件
                    from_wxid = message["FromWxid"]
                    sender_wxid = message.get("SenderWxid", from_wxid)
                    self.cache_file(sender_wxid, binary_file_data, file_name, mime_type)

                    # 如果是私聊，也缓存到聊天对象的ID
                    if from_wxid != sender_wxid:
                        self.cache_file(from_wxid, binary_file_data, file_name, mime_type)

                    logger.info(f"文件下载成功并已缓存: {file_name}, 大小: {len(binary_file_data)/1024:.2f} KB")
                else:
                    logger.warning("Dify: 所有API端点尝试失败")
        except Exception as e:
            logger.error(f"Dify: 处理XML消息时发生错误: {str(e)}")
            logger.error(traceback.format_exc())

        return True  # 允许后续插件处理

    @on_file_message(priority=20)
    async def handle_file(self, bot: WechatAPIClient, message: dict):
        """处理文件消息"""
        if not self.enable:
            return

        try:
            # 获取文件消息的关键信息
            msg_id = message.get("MsgId")
            from_wxid = message.get("FromWxid")
            sender_wxid = message.get("SenderWxid")
            file_content = message.get("Content")

            logger.info(f"收到文件消息: MsgId={msg_id}, FromWxid={from_wxid}, SenderWxid={sender_wxid}")

            # 如果Content是二进制数据，直接使用
            if isinstance(file_content, bytes) and len(file_content) > 0:
                logger.info(f"文件内容是二进制数据，大小: {len(file_content)} 字节")

                # 获取文件名和类型
                file_name = message.get("FileName", f"file_{int(time.time())}")

                # 检测文件类型
                mime_type = "application/octet-stream"  # 默认类型
                try:
                    kind = filetype.guess(file_content)
                    if kind is not None:
                        mime_type = kind.mime
                        # 如果文件名没有后缀，添加正确的后缀
                        if not os.path.splitext(file_name)[1]:
                            file_name = f"{file_name}.{kind.extension}"
                except Exception as e:
                    logger.error(f"检测文件类型失败: {e}")

            # 如果Content是XML字符串，解析并下载文件
            elif isinstance(file_content, str) and ("<appmsg" in file_content or "<msg>" in file_content):
                logger.info("文件内容是XML格式，尝试解析并下载文件")
                try:
                    # 解析XML
                    import xml.etree.ElementTree as ET
                    import mimetypes
                    import base64

                    # 处理可能的XML格式差异
                    if "<msg>" in file_content and "<appmsg" in file_content:
                        # 提取<appmsg>部分
                        start = file_content.find("<appmsg")
                        end = file_content.find("</appmsg>") + 9
                        appmsg_xml = file_content[start:end]
                        root = ET.fromstring(f"<root>{appmsg_xml}</root>")
                        appmsg = root.find('appmsg')
                    else:
                        root = ET.fromstring(file_content)
                        appmsg = root.find('.//appmsg')

                    if appmsg is not None:
                        # 获取文件名
                        title = appmsg.find('.//title')
                        file_name = title.text if title is not None and title.text else f"file_{int(time.time())}"

                        # 获取文件类型
                        fileext = appmsg.find('.//fileext')
                        if fileext is not None and fileext.text:
                            ext = fileext.text.lower()
                            if not file_name.lower().endswith(f".{ext}"):
                                file_name = f"{file_name}.{ext}"
                            mime_type = mimetypes.guess_type(file_name)[0] or "application/octet-stream"
                        else:
                            mime_type = "application/octet-stream"

                        # 获取下载所需信息
                        appattach = appmsg.find('.//appattach')
                        if appattach is not None:
                            attachid = appattach.find('.//attachid')
                            aeskey = appattach.find('.//aeskey')
                            totallen = appattach.find('.//totallen')

                            # 获取文件大小
                            total_len = int(totallen.text) if totallen is not None and totallen.text and totallen.text.isdigit() else 0

                            # 获取附件ID和其他下载所需信息
                            attach_id = None
                            cdn_url = None
                            aes_key = None

                            if attachid is not None and attachid.text:
                                attach_id = attachid.text.strip()
                                logger.info(f"找到附件ID: {attach_id}")

                            # 获取CDN URL和AES密钥（用于方法3）
                            cdnattachurl = appattach.find('.//cdnattachurl')
                            if cdnattachurl is not None and cdnattachurl.text:
                                cdn_url = cdnattachurl.text.strip()
                                logger.info(f"找到CDN URL: {cdn_url}")

                            if aeskey is not None and aeskey.text:
                                aes_key = aeskey.text.strip()
                                logger.info(f"找到AES密钥: {aes_key}")

                                # 开始下载文件
                                logger.info(f"开始下载文件: {file_name}, 大小: {total_len} 字节")

                                # 尝试不同的下载方法
                                try:
                                    file_data = None

                                    # 方法1: 如果有附件ID，使用download_attach方法
                                    if attach_id:
                                        logger.debug(f"方法1: 尝试使用download_attach方法下载文件，附件ID: {attach_id}")
                                        file_data = await bot.download_attach(attach_id)

                                    # 方法3: 如果有CDN URL和AES密钥，使用download_image方法
                                    if not file_data and cdn_url and aes_key:
                                        logger.debug(f"方法3: 尝试使用download_image方法下载文件，CDN URL: {cdn_url}")
                                        try:
                                            image_data = await bot.download_image(aes_key, cdn_url)
                                            if image_data:
                                                if isinstance(image_data, str):
                                                    try:
                                                        file_data = base64.b64decode(image_data)
                                                        logger.info(f"使用download_image成功下载文件，大小: {len(file_data)} 字节")
                                                    except Exception as e:
                                                        logger.error(f"Base64解码失败: {e}")
                                        except Exception as e:
                                            logger.error(f"download_image方法失败: {e}")
                                    if not file_data:
                                        # 方法2: 使用Tools/DownloadFile API分段下载文件
                                        logger.debug(f"尝试使用Tools/DownloadFile API分段下载文件")

                                        # 分段下载大文件
                                        chunk_size = 64 * 1024  # 64KB
                                        chunks = (total_len + chunk_size - 1) // chunk_size  # 向上取整
                                        file_data_bytes = bytearray()
                                        download_success = False

                                        # 尝试两个不同的API端点
                                        urls = [
                                            f'http://{bot.ip}:{bot.port}/api/Tools/DownloadFile',
                                            f'http://{bot.ip}:{bot.port}/VXAPI/Tools/DownloadFile'
                                        ]

                                        # 尝试每个API端点
                                        for url in urls:
                                            if download_success:
                                                break

                                            logger.info(f"尝试使用 {url} 分段下载文件，总大小: {total_len} 字节，分 {chunks} 段下载")
                                            file_data_bytes.clear()  # 清空之前的数据

                                            try:
                                                async with aiohttp.ClientSession() as session:
                                                    # 分段下载
                                                    for i in range(chunks):
                                                        start_pos = i * chunk_size
                                                        # 最后一段可能不足 chunk_size
                                                        current_chunk_size = min(chunk_size, total_len - start_pos)

                                                        logger.debug(f"下载第 {i+1}/{chunks} 段，起始位置: {start_pos}，大小: {current_chunk_size} 字节")

                                                        # 构造请求参数
                                                        json_param = {
                                                            "AppID": "",  # 可选参数
                                                            "AttachId": attach_id,
                                                            "DataLen": total_len,
                                                            "Section": {
                                                                "DataLen": current_chunk_size,
                                                                "StartPos": start_pos
                                                            },
                                                            "UserName": "",  # 可选参数
                                                            "Wxid": bot.wxid
                                                        }

                                                        # 设置较长的超时时间
                                                        timeout = aiohttp.ClientTimeout(total=60)  # 1分钟

                                                        # 发送请求
                                                        try:
                                                            async with session.post(url, json=json_param, timeout=timeout) as resp:
                                                                if resp.status == 200:
                                                                    resp_json = await resp.json()
                                                                    if resp_json.get("Success"):
                                                                        data = resp_json.get("Data")
                                                                        if isinstance(data, str):
                                                                            try:
                                                                                chunk_data = base64.b64decode(data)
                                                                                file_data_bytes.extend(chunk_data)
                                                                                logger.debug(f"第 {i+1}/{chunks} 段下载成功，大小: {len(chunk_data)} 字节")
                                                                            except Exception as e:
                                                                                logger.error(f"Base64解码失败: {e}")
                                                                                break
                                                                        elif isinstance(data, dict) and "buffer" in data:
                                                                            try:
                                                                                chunk_data = base64.b64decode(data["buffer"])
                                                                                file_data_bytes.extend(chunk_data)
                                                                                logger.debug(f"第 {i+1}/{chunks} 段下载成功，大小: {len(chunk_data)} 字节")
                                                                            except Exception as e:
                                                                                logger.error(f"Buffer Base64解码失败: {e}")
                                                                                break
                                                                        else:
                                                                            logger.warning(f"无法解析响应数据: {data}")
                                                                            break
                                                                    else:
                                                                        logger.warning(f"API返回错误: {resp_json}")
                                                                        break
                                                                else:
                                                                    logger.warning(f"API请求失败: {resp.status}")
                                                                    break
                                                        except Exception as e:
                                                            logger.error(f"下载第 {i+1}/{chunks} 段时出错: {e}")
                                                            break

                                                    # 检查文件是否下载完整
                                                    if len(file_data_bytes) > 0:
                                                        logger.info(f"文件分段下载成功，实际大小: {len(file_data_bytes)} 字节")
                                                        file_data = base64.b64encode(file_data_bytes).decode('utf-8')
                                                        download_success = True
                                                        break
                                                    else:
                                                        logger.warning(f"文件下载失败，数据为空")
                                            except Exception as e:
                                                logger.error(f"尝试使用 {url} 分段下载文件时出错: {e}")
                                                logger.error(traceback.format_exc())

                                        # 如果所有尝试都失败
                                        if not download_success:
                                            logger.error("所有API端点尝试失败")
                                except Exception as e:
                                    logger.error(f"下载文件异常: {e}")
                                    logger.error(traceback.format_exc())
                                    file_data = None

                                if file_data:
                                    # 如果返回的是base64字符串，解码为二进制
                                    if isinstance(file_data, str):
                                        try:
                                            file_content = base64.b64decode(file_data)
                                        except Exception as e:
                                            logger.error(f"Base64解码失败: {e}")
                                            file_content = file_data.encode('utf-8')
                                    elif isinstance(file_data, dict) and "buffer" in file_data:
                                        try:
                                            file_content = base64.b64decode(file_data["buffer"])
                                        except Exception as e:
                                            logger.error(f"Buffer Base64解码失败: {e}")
                                            file_content = str(file_data).encode('utf-8')
                                    else:
                                        file_content = str(file_data).encode('utf-8')

                                    logger.info(f"文件下载成功，大小: {len(file_content)} 字节")
                                else:
                                    logger.error("文件下载失败或内容为空")
                                    await bot.send_text_message(from_wxid, "文件下载失败，请重新发送。")
                                    return
                            else:
                                logger.error("XML中缺少必要的附件ID")
                                await bot.send_text_message(from_wxid, "无法解析文件信息，请重新发送。")
                                return
                        else:
                            logger.error("XML中缺少appattach节点")
                            await bot.send_text_message(from_wxid, "无法解析文件信息，请重新发送。")
                            return
                    else:
                        logger.error("XML格式不正确，无法解析appmsg节点")
                        await bot.send_text_message(from_wxid, "无法解析文件信息，请重新发送。")
                        return
                except Exception as e:
                    logger.error(f"解析XML或下载文件失败: {e}")
                    logger.error(traceback.format_exc())
                    await bot.send_text_message(from_wxid, f"处理文件失败: {str(e)}")
                    return
            else:
                logger.warning(f"文件内容格式不支持: {type(file_content)}")
                await bot.send_text_message(from_wxid, "不支持的文件格式，请重新发送。")
                return

            # 缓存文件
            self.cache_file(sender_wxid, file_content, file_name, mime_type)

            # 如果是私聊，也缓存到聊天对象的ID
            if from_wxid != sender_wxid:
                self.cache_file(from_wxid, file_content, file_name, mime_type)

            logger.info(f"文件已缓存: {file_name}, 大小: {len(file_content)/1024:.2f} KB, 类型: {mime_type}")

        except Exception as e:
            logger.error(f"处理文件消息失败: {e}")
            logger.error(traceback.format_exc())

    async def send_quote_message(self, bot: WechatAPIClient, to_wxid: str, content: str, quoted_msg_id: str,
                              quoted_wxid: str, quoted_nickname: str, quoted_content: str):
        """
        发送引用消息 - 现在直接发送普通文本消息

        参数:
            bot: WechatAPIClient实例
            to_wxid: 消息接收人的wxid
            content: 要发送的新消息内容
            quoted_msg_id: 被引用消息的newMsgId (不再使用)
            quoted_wxid: 被引用消息发送者的wxid (不再使用)
            quoted_nickname: 被引用消息发送者的昵称 (不再使用)
            quoted_content: 被引用的消息内容 (不再使用)
        """
        # 直接发送普通文本消息，不使用引用格式
        logger.info(f"发送普通文本消息，内容: {content[:30]}...")
        return await bot.send_text_message(to_wxid, content)