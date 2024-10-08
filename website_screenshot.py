#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Script Name: Website Screenshot Taker
Version: 1.2.3
Author: Quentin King
Date: 09-22-2024

Description:
This script automates the process of taking screenshots of specified websites using Selenium WebDriver,
combines the screenshots into a grid image, uploads the image to an FTP server, and sends notifications
via Pushover. It includes robust error handling, resource monitoring, and a graceful shutdown mechanism.
Additionally, it automates the ChromeDriver update process to ensure compatibility with the installed Chrome browser.

Enhancements:
- Type hinting for static type checking.
- Validation of configuration files.
- Enhanced logging with contextual information.
- Retry logic with exponential backoff for network calls.
- Timeouts for WebDriver operations.
- Context managers for resource management.
- Signal handling for additional signals (`SIGHUP`, `SIGQUIT`).
- Validation of environment variables.
- Graceful degradation.
- **New Feature**: Checks if Chrome is running at the start and shuts it down if necessary.
"""

import os
import shutil
import time
import re
import requests
import zipfile
import threading
import functools
import signal
import random
from datetime import datetime, timedelta
import ftplib
from PIL import Image, ImageDraw, ImageFont, UnidentifiedImageError
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from selenium.common.exceptions import (
    WebDriverException,
    TimeoutException,
    SessionNotCreatedException,
)
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from dotenv import load_dotenv
import yaml
from tqdm import tqdm
import psutil
import logging
from logging.handlers import RotatingFileHandler
from pythonjsonlogger import jsonlogger
from pydantic import BaseModel, ValidationError, field_validator
from typing import Optional, Tuple, Dict, List, Any, Callable
import signal
import psutil
import os
import signal

# =============================================================================
# Configuration Validation using Pydantic V2
# =============================================================================

class Config(BaseModel):
    debug_mode: bool = False
    log_dir: str
    screenshot_dir: str
    archive_dir: str
    driver_dir: str  # Directory to store ChromeDriver
    websites: List[str]
    grid_size: Dict[str, int]
    profile_path: str
    headless: bool = True
    window_size: Dict[str, int]
    max_workers: int = 5

    @field_validator('grid_size')
    def check_grid_size(cls, v: Dict[str, int]) -> Dict[str, int]:
        if 'rows' not in v or 'columns' not in v:
            raise ValueError("Grid size must include 'rows' and 'columns'")
        return v

    @field_validator('window_size')
    def check_window_size(cls, v: Dict[str, int]) -> Dict[str, int]:
        if 'width' not in v or 'height' not in v:
            raise ValueError("Window size must include 'width' and 'height'")
        return v

# =============================================================================
# Load Configuration and Environment Variables
# =============================================================================

# Get the directory where the script is located
script_dir = os.path.dirname(os.path.abspath(__file__))

# Load environment variables from .env file
dotenv_path = os.path.join(script_dir, '.env')
load_dotenv(dotenv_path)

# Load configuration from config.yaml
config_path = os.path.join(script_dir, 'config.yaml')
try:
    with open(config_path, 'r') as file:
        config_data = yaml.safe_load(file)
    config = Config(**config_data)
except ValidationError as e:
    print(f"Configuration validation error: {e}")
    exit(1)
except FileNotFoundError:
    print(f"Configuration file not found at {config_path}")
    exit(1)

# Assign non-sensitive configurations
websites: List[str] = config.websites
grid_size: Tuple[int, int] = (
    config.grid_size.get('rows', 3),
    config.grid_size.get('columns', 5),
)
window_size: Tuple[int, int] = (
    config.window_size.get('width', 1920),
    config.window_size.get('height', 1080),
)

# Create necessary directories
os.makedirs(config.log_dir, exist_ok=True)
os.makedirs(config.screenshot_dir, exist_ok=True)
os.makedirs(config.archive_dir, exist_ok=True)
os.makedirs(config.driver_dir, exist_ok=True)  # Ensure driver directory exists

# =============================================================================
# Setup Logging with Contextual Information and Structured JSON Logging
# =============================================================================

log_file = os.path.join(config.log_dir, 'website_refresh_log.json')

# Configure root logger
logger = logging.getLogger()
logger.setLevel(logging.DEBUG if config.debug_mode else logging.INFO)

# Rotating file handler with JSON formatter
file_handler = RotatingFileHandler(log_file, maxBytes=5 * 1024 * 1024, backupCount=5)
file_handler.setLevel(logging.DEBUG if config.debug_mode else logging.INFO)
file_formatter = jsonlogger.JsonFormatter(
    '%(asctime)s %(levelname)s %(message)s %(funcName)s %(lineno)d'
)
file_handler.setFormatter(file_formatter)
logger.addHandler(file_handler)

# Console handler with simple formatter
console_handler = logging.StreamHandler()
console_handler.setLevel(logging.DEBUG if config.debug_mode else logging.INFO)
console_formatter = logging.Formatter(
    '%(asctime)s - %(levelname)s - %(message)s - %(funcName)s - Line: %(lineno)d'
)
console_handler.setFormatter(console_formatter)
logger.addHandler(console_handler)

# Suppress debug logs from external libraries
logging.getLogger('PIL').setLevel(logging.WARNING)
logging.getLogger('urllib3').setLevel(logging.WARNING)
logging.getLogger('selenium').setLevel(logging.WARNING)
logging.getLogger('ftplib').setLevel(logging.WARNING)
logging.getLogger('requests').setLevel(logging.WARNING)

logger.info("Script started successfully!")

# =============================================================================
# New Feature: Check if Chrome is Open and Shut It Down if Necessary
# =============================================================================

def is_chrome_open() -> bool:
    """
    Check if Chrome browser is open by scanning for any running 'chrome' processes.

    Returns:
        bool: True if Chrome is running, False otherwise.
    """
    try:
        for proc in psutil.process_iter(['pid', 'name']):
            if 'chrome' in proc.info['name'].lower():
                return True
        return False
    except Exception as e:
        logger.error(f"Error checking Chrome processes: {e}", exc_info=True)
        return False

def shut_down_chrome() -> None:
    """
    Shut down all instances of the Chrome browser.
    """
    try:
        for proc in psutil.process_iter(['pid', 'name']):
            if 'chrome' in proc.info['name'].lower():
                try:
                    proc.terminate()
                    proc.wait(timeout=5)
                    logger.info(f"Terminated Chrome process with PID: {proc.info['pid']}")
                except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.TimeoutExpired) as e:
                    logger.warning(f"Failed to terminate Chrome process PID {proc.info['pid']}: {e}")
    except Exception as e:
        logger.error(f"Unexpected error while shutting down Chrome: {e}", exc_info=True)

# Check if Chrome is open and shut it down if necessary
if is_chrome_open():
    logger.info("Chrome is currently open. Shutting it down...")
    shut_down_chrome()
else:
    logger.info("Chrome is not running. Proceeding with the script...")

# =============================================================================
# FTP and Pushover Credentials (Loaded from .env)
# =============================================================================

# FTP credentials
ftp_host: Optional[str] = os.getenv('FTP_HOST')
ftp_user: Optional[str] = os.getenv('FTP_USER')
ftp_pass: Optional[str] = os.getenv('FTP_PASS')
ftp_port: int = int(os.getenv('FTP_PORT', 21))  # Default FTP port is 21

# Pushover setup
pushover_user_key: Optional[str] = os.getenv('PUSHOVER_USER_KEY')
pushover_token: Optional[str] = os.getenv('PUSHOVER_TOKEN')

# Base URL for accessing the uploaded image
base_url: str = os.getenv('BASE_URL', '').rstrip('/') + '/'

# Validate environment variables
required_env_vars = {
    'FTP_HOST': ftp_host,
    'FTP_USER': ftp_user,
    'FTP_PASS': ftp_pass,
    'PUSHOVER_USER_KEY': pushover_user_key,
    'PUSHOVER_TOKEN': pushover_token,
    'BASE_URL': base_url,
}

missing_env_vars = [key for key, value in required_env_vars.items() if not value]
if missing_env_vars:
    logger.error(f"Missing environment variables: {', '.join(missing_env_vars)}")
    exit(1)

# =============================================================================
# Global Variables for Resource Monitoring and Shutdown
# =============================================================================

# Resource usage lists
cpu_usages: List[float] = []
ram_usages: List[float] = []
disk_read_bytes: List[int] = []
disk_write_bytes: List[int] = []
net_sent_bytes: List[int] = []
net_recv_bytes: List[int] = []

# Shutdown event for graceful shutdown
shutdown_event = threading.Event()

# Resource monitor event
resource_monitor_event = threading.Event()

# Flag to indicate if a shutdown signal was received
shutdown_signal_received: bool = False

# Variables for execution statistics
successful_sites: List[str] = []
failed_sites: Dict[str, str] = {}

# Last notification time for throttling
last_notification_time: Optional[datetime] = None

# Initialize combined_image_path as None
combined_image_path: Optional[str] = None

# =============================================================================
# Utility Functions
# =============================================================================

def send_pushover_notification(
    start_time: datetime,
    end_time: datetime,
    total_time: timedelta,
    avg_cpu_usage: float,
    avg_ram_usage: float,
    combined_image_url: Optional[str],
    total_disk_read: int,
    total_disk_write: int,
    total_net_sent: int,
    total_net_recv: int,
    error_occurred: bool = False,
    error_details: Optional[str] = None
) -> None:
    """
    Send a notification via Pushover with the script's results, including detailed information.
    """
    global last_notification_time

    start_time_formatted = start_time.strftime("%A, %B %d, %Y, at %H:%M")
    end_time_formatted = end_time.strftime("%A, %B %d, %Y, at %H:%M")
    total_time_formatted = str(total_time).split('.')[0]  # Remove microseconds

    total_sites = len(successful_sites) + len(failed_sites)
    num_successful = len(successful_sites)
    num_failed = len(failed_sites)

    # Build the message
    if error_occurred or num_failed > 0:
        emoji = "❌"
        title = f"{emoji} Website Screenshot Script Encountered Errors"
        message = f"{emoji} <b>Website Screenshot Script Encountered Errors</b><br/><br/>"
    else:
        emoji = "✅"
        title = f"{emoji} Website Screenshot Script Completed Successfully!"
        message = f"{emoji} <b>Website Screenshot Script Completed Successfully!</b><br/><br/>"

    # Summary Table
    message += "<b>Summary:</b><br/>"
    message += (
        f"- 🌐 Websites Processed: {total_sites}<br/>"
        f"- ✅ Successful: {num_successful}<br/>"
        f"- ❌ Failed: {num_failed}<br/>"
    )

    if num_failed > 0:
        message += "<br/>🚫 <b>Websites That Failed:</b><br/>"
        for site, error in failed_sites.items():
            message += f"- {site}: {error}<br/>"

    # Performance Metrics
    message += "<br/><b>Performance Metrics:</b><br/>"
    message += (
        f"- ⏱️ Total Time Taken: {total_time_formatted}<br/>"
        f"- 💻 Average CPU Usage: {avg_cpu_usage:.1f}%<br/>"
        f"- 📈 Average RAM Usage: {avg_ram_usage:.1f}%<br/>"
        f"- 💾 Total Disk Read: {total_disk_read / (1024 * 1024):.2f} MB<br/>"
        f"- 💿 Total Disk Write: {total_disk_write / (1024 * 1024):.2f} MB<br/>"
        f"- 📤 Total Network Sent: {total_net_sent / (1024 * 1024):.2f} MB<br/>"
        f"- 📥 Total Network Received: {total_net_recv / (1024 * 1024):.2f} MB<br/>"
    )

    # Start and end times
    message += "<br/><b>Execution Time:</b><br/>"
    message += f"- 🕐 Started At: {start_time_formatted}<br/>"
    message += f"- 🕔 Completed At: {end_time_formatted}<br/>"

    # Add combined image link if available
    if combined_image_url:
        message += f"<br/>📷 <a href=\"{combined_image_url}\">View Combined Screenshot</a><br/>"

    # Add error details if any
    if error_occurred and error_details:
        message += f"<br/>⚠️ <b>Error Details:</b><br/>{error_details}<br/>"

    # Set notification priority and sound based on error occurrence
    if error_occurred or num_failed > 0:
        priority = 1  # Warning
        sound = "siren"
    else:
        priority = 0  # General update
        sound = "pushover"

    # Implement notification throttling (send notification only if more than 1 hour has passed since last)
    current_time = datetime.now()
    if last_notification_time and (current_time - last_notification_time).total_seconds() < 3600:
        logger.info("Notification throttled to prevent spamming.")
        return
    last_notification_time = current_time

    # Build the payload
    payload = {
        "token": pushover_token,
        "user": pushover_user_key,
        "message": message,
        "title": title,
        "html": 1,  # Enable HTML formatting
        "priority": priority,
        "sound": sound,
    }

    logger.info("Sending Pushover notification...")

    # Send the notification with retry logic
    try:
        send_with_retry(
            func=requests.post,
            url="https://api.pushover.net/1/messages.json",
            data=payload,
            exceptions=(requests.RequestException,),
            total_tries=3,
            initial_wait=2,
            backoff_factor=2,
        )
        logger.info("Pushover notification sent successfully!")
    except Exception as e:
        logger.error(f"Error sending Pushover notification: {e}", exc_info=True)

def calculate_resource_usage() -> Tuple[float, float, psutil._common.sdiskio, psutil._common.snetio]:
    """
    Calculate CPU, RAM, Disk I/O, and Network usage.

    Returns:
        tuple: CPU usage, RAM usage, Disk I/O read/write bytes, Network I/O sent/recv bytes.
    """
    cpu_usage = psutil.cpu_percent(interval=1)
    ram_usage = psutil.virtual_memory().percent
    disk_io = psutil.disk_io_counters()
    net_io = psutil.net_io_counters()
    return cpu_usage, ram_usage, disk_io, net_io

def monitor_resources() -> None:
    """
    Monitor resource usage over time.
    """
    while not resource_monitor_event.is_set():
        cpu_usage, ram_usage, disk_io, net_io = calculate_resource_usage()
        cpu_usages.append(cpu_usage)
        ram_usages.append(ram_usage)
        disk_read_bytes.append(disk_io.read_bytes)
        disk_write_bytes.append(disk_io.write_bytes)
        net_sent_bytes.append(net_io.bytes_sent)
        net_recv_bytes.append(net_io.bytes_recv)
        time.sleep(5)
    logger.info("Resource monitor thread exiting due to resource_monitor_event.")

def retry(
    exceptions: Tuple[Exception, ...],
    total_tries: int = 4,
    initial_wait: float = 0.5,
    backoff_factor: int = 2
) -> Callable:
    """
    Decorator for retrying a function with exponential backoff.

    Parameters:
        exceptions (tuple): Exceptions to catch.
        total_tries (int): Total number of attempts.
        initial_wait (float): Initial wait time in seconds.
        backoff_factor (int): Multiplier for exponential backoff.

    Returns:
        function: Wrapped function with retry logic.
    """
    def decorator_retry(func: Callable) -> Callable:
        @functools.wraps(func)
        def wrapper_retry(*args: Any, **kwargs: Any) -> Any:
            _tries, _delay = total_tries, initial_wait
            while _tries > 1:
                try:
                    return func(*args, **kwargs)
                except exceptions as e:
                    if shutdown_event.is_set():
                        logger.info(f"Shutdown event detected during retries. Exiting {func.__name__}.")
                        raise e
                    msg = f"{func.__name__} failed with {e}, retrying in {_delay} seconds..."
                    logger.warning(msg)
                    time.sleep(_delay)
                    _tries -= 1
                    _delay *= backoff_factor
            return func(*args, **kwargs)
        return wrapper_retry
    return decorator_retry

def send_with_retry(
    func: Callable,
    *args: Any,
    exceptions: Tuple[Exception, ...],
    total_tries: int = 3,
    initial_wait: float = 2,
    backoff_factor: int = 2,
    **kwargs: Any
) -> Any:
    """
    Send a request with retry logic.

    Parameters:
        func (Callable): The function to execute.
        exceptions (tuple): Exceptions to catch.
        total_tries (int): Total number of attempts.
        initial_wait (float): Initial wait time in seconds.
        backoff_factor (int): Multiplier for exponential backoff.

    Returns:
        Any: The result of the function call.
    """
    _tries, _delay = total_tries, initial_wait
    while _tries > 1:
        try:
            return func(*args, **kwargs)
        except exceptions as e:
            if shutdown_event.is_set():
                logger.info(f"Shutdown event detected during retries. Exiting {func.__name__}.")
                raise e
            msg = f"{func.__name__} failed with {e}, retrying in {_delay} seconds..."
            logger.warning(msg)
            time.sleep(_delay)
            _tries -= 1
            _delay *= backoff_factor
    return func(*args, **kwargs)

def add_timestamp_to_image(image_path: str) -> None:
    """
    Add a timestamp watermark to the image.

    Parameters:
        image_path (str): Path to the image file.
    """
    try:
        img = Image.open(image_path).convert('RGBA')
        txt_layer = Image.new('RGBA', img.size, (255,255,255,0))
        draw = ImageDraw.Draw(txt_layer)
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        font = ImageFont.load_default()

        # Using textbbox to get the bounding box of the text
        bbox = draw.textbbox((0, 0), timestamp, font=font)
        text_width = bbox[2] - bbox[0]
        text_height = bbox[3] - bbox[1]

        position = (img.width - text_width - 20, img.height - text_height - 20)
        # Draw semi-transparent rectangle behind the text
        rectangle_position = (
            position[0] - 10,
            position[1] - 10,
            position[0] + text_width + 10,
            position[1] + text_height + 10
        )
        draw.rectangle(rectangle_position, fill=(0, 0, 0, 128))
        # Draw text over the rectangle
        draw.text(position, timestamp, fill=(255, 255, 255, 255), font=font)
        combined = Image.alpha_composite(img, txt_layer)
        combined = combined.convert('RGB')  # Convert back to RGB
        combined.save(image_path, format='PNG', optimize=True)
        logger.info(f"Timestamp added to image: {image_path}")
    except (UnidentifiedImageError, Exception) as e:
        logger.error(f"Failed to add timestamp to image {image_path}: {e}", exc_info=True)

def get_latest_stable_chromedriver_version() -> Optional[str]:
    """
    Get the latest stable ChromeDriver version.

    Returns:
        str: Latest stable ChromeDriver version (e.g., "129.0.6668.58") or None if failed.
    """
    try:
        response = requests.get(
            "https://googlechromelabs.github.io/chrome-for-testing/last-known-good-versions.json",
            timeout=10
        )
        response.raise_for_status()
        data = response.json()
        stable_version = data.get('channels', {}).get('Stable', {}).get('version')
        if stable_version:
            return stable_version
        else:
            logger.error("Failed to get the stable ChromeDriver version from the JSON data.")
    except Exception as e:
        logger.error(f"Error while fetching ChromeDriver version: {e}", exc_info=True)
    return None

def download_and_extract_chromedriver(version: str, destination: str) -> bool:
    """
    Download and extract ChromeDriver from the constructed URL.

    Parameters:
        version (str): ChromeDriver version to download.
        destination (str): Directory where ChromeDriver should be extracted.

    Returns:
        bool: True if download and extraction succeeded, False otherwise.
    """
    # Adjust the download URL based on your OS if necessary
    base_download_url = f"https://edgedl.me.gvt1.com/edgedl/chrome/chrome-for-testing/{version}/win64/chromedriver-win64.zip"
    zip_path = os.path.join(destination, "chromedriver.zip")

    try:
        logger.info(f"Downloading ChromeDriver from {base_download_url}")
        response = requests.get(base_download_url, stream=True, timeout=60)
        response.raise_for_status()

        with open(zip_path, 'wb') as f:
            shutil.copyfileobj(response.raw, f)
        logger.info(f"Downloaded ChromeDriver to {zip_path}")

        # Extract the zip file
        with zipfile.ZipFile(zip_path, 'r') as zip_ref:
            zip_ref.extractall(destination)
        logger.info(f"Extracted ChromeDriver to {destination}")

        # Remove the zip file
        os.remove(zip_path)
        logger.info(f"Removed temporary zip file {zip_path}")

        return True
    except Exception as e:
        logger.error(f"Failed to download or extract ChromeDriver: {e}", exc_info=True)
        return False

def check_chromedriver() -> bool:
    """
    Check if ChromeDriver is compatible with Chrome.

    Returns:
        bool: True if compatible, False otherwise.
    """
    chromedriver_path = os.path.join(config.driver_dir, "chromedriver.exe")
    try:
        driver = webdriver.Chrome(service=Service(chromedriver_path))
        driver.quit()
    except Exception as e:
        logger.error(f"ChromeDriver issue detected: {e}", exc_info=True)
        return False
    return True

@retry(
    (WebDriverException, SessionNotCreatedException, TimeoutException, ValueError),
    total_tries=4,
    initial_wait=2,
    backoff_factor=2
)
def initialize_webdriver() -> webdriver.Chrome:
    """
    Initialize the Selenium WebDriver with options. If initialization fails due to ChromeDriver issues,
    attempt to update the ChromeDriver and retry.

    Returns:
        WebDriver: Selenium WebDriver instance.
    """
    if shutdown_event.is_set():
        logger.info("Shutdown event detected. Skipping WebDriver initialization.")
        raise Exception("Shutdown event detected.")

    options_var = webdriver.ChromeOptions()
    profile_path = config.profile_path
    options_var.add_argument(r"--user-data-dir=" + profile_path)
    options_var.add_argument(r'--profile-directory=Default')
    if config.headless:
        options_var.add_argument('--headless')
        options_var.add_argument('--disable-gpu')

    # Set consistent window size
    options_var.add_argument(f'--window-size={window_size[0]},{window_size[1]}')

    # Additional options for headless operation
    options_var.add_argument('--no-sandbox')
    options_var.add_argument('--disable-dev-shm-usage')

    # Set page load strategy to 'normal' to wait for all resources
    options_var.page_load_strategy = 'normal'

    chromedriver_path = os.path.join(config.driver_dir, "chromedriver.exe")

    try:
        if not os.path.exists(chromedriver_path):
            logger.info("ChromeDriver not found. Fetching the latest stable version.")
            latest_version = get_latest_stable_chromedriver_version()
            if latest_version:
                download_success = download_and_extract_chromedriver(latest_version, config.driver_dir)
                if not download_success:
                    raise Exception("Failed to download the latest ChromeDriver.")
            else:
                raise Exception("Could not retrieve the latest ChromeDriver version.")

        # Attempt to initialize WebDriver
        driver = webdriver.Chrome(service=Service(chromedriver_path), options=options_var)
        logger.info("WebDriver initialized successfully.")
        return driver
    except (WebDriverException, SessionNotCreatedException, TimeoutException, ValueError) as e:
        logger.error(f"Failed to initialize WebDriver: {e}", exc_info=True)
        logger.info("Attempting to update ChromeDriver.")

        # Step 1: Scrape the latest stable ChromeDriver version
        latest_version = get_latest_stable_chromedriver_version()
        if latest_version:
            logger.info(f"Latest stable ChromeDriver version: {latest_version}")

            # Step 2: Download and extract the latest ChromeDriver
            download_success = download_and_extract_chromedriver(latest_version, config.driver_dir)
            if download_success:
                # Step 3: Retry initializing WebDriver with the new driver
                try:
                    driver = webdriver.Chrome(service=Service(chromedriver_path), options=options_var)
                    logger.info("WebDriver initialized successfully with the updated ChromeDriver.")
                    return driver
                except Exception as retry_e:
                    logger.error(f"Retrying WebDriver initialization failed: {retry_e}", exc_info=True)
        else:
            logger.error("Could not retrieve the latest ChromeDriver version.")

        # If all attempts fail, raise the exception to be handled in main
        raise e

def archive_old_screenshots() -> None:
    """
    Archive old screenshots and clean up old archives.
    """
    try:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        archive_subdir = os.path.join(config.archive_dir, f"archive_{timestamp}")
        os.makedirs(archive_subdir, exist_ok=True)

        # Move existing screenshots to archive
        for filename in os.listdir(config.screenshot_dir):
            if filename.endswith('.png'):
                shutil.move(
                    os.path.join(config.screenshot_dir, filename),
                    os.path.join(archive_subdir, filename)
                )
        logger.info(f"Old screenshots moved to {archive_subdir}")

        # Cleanup old archives, keep only the 5 most recent
        archives = sorted(os.listdir(config.archive_dir), reverse=True)
        if len(archives) > 5:
            archives_to_delete = archives[5:]  # Keep the first 5 (most recent)
            for archive in archives_to_delete:
                archive_path = os.path.join(config.archive_dir, archive)
                shutil.rmtree(archive_path)
                logger.info(f"Deleted old archive: {archive_path}")
    except Exception as e:
        logger.error(f"Failed to archive old screenshots: {e}", exc_info=True)

@retry(
    (Exception,),
    total_tries=3,
    initial_wait=2,
    backoff_factor=2
)
def upload_to_ftp(file_path: str) -> bool:
    """
    Upload the combined image to the FTP server.

    Parameters:
        file_path (str): Path to the file to upload.

    Returns:
        bool: True if upload succeeded, False otherwise.
    """
    if shutdown_signal_received:
        logger.info("Shutdown signal received. Skipping FTP upload.")
        raise Exception("Shutdown event detected.")

    try:
        with ftplib.FTP(timeout=30) as ftp:
            ftp.connect(ftp_host, ftp_port)
            ftp.login(ftp_user, ftp_pass)
            ftp.set_pasv(True)  # Enable passive mode

            # Delete all existing image files in the FTP directory
            try:
                files = ftp.nlst()
            except ftplib.error_perm as e:
                if str(e).startswith('550'):
                    files = []
                else:
                    raise e

            for f in files:
                if f.lower().endswith(('.png', '.jpg', '.jpeg')):
                    try:
                        ftp.delete(f)
                        logger.info(f"Deleted existing file: {f}")
                    except ftplib.error_perm as e:
                        logger.warning(f"Could not delete file {f}: {e}")

            # Upload the new file
            filename = os.path.basename(file_path)
            with open(file_path, 'rb') as file:
                ftp.storbinary(f'STOR {filename}', file)
            logger.info(f"Uploaded {filename} to FTP successfully")
            return True
    except Exception as e:
        logger.error(f"FTP upload failed: {e}", exc_info=True)
        raise e

def combine_images_into_grid(screenshot_dir: str, grid_size: Tuple[int, int]) -> Optional[str]:
    """
    Combine screenshots into a grid image.

    Parameters:
        screenshot_dir (str): Directory containing screenshots.
        grid_size (tuple): Grid size as (rows, columns).

    Returns:
        str: Path to the combined image or None if no images found.
    """
    try:
        images = []
        for filename in os.listdir(screenshot_dir):
            if filename.endswith('.png'):
                img = Image.open(os.path.join(screenshot_dir, filename))
                if img.mode != 'RGB':
                    img = img.convert('RGB')
                images.append(img)

        if not images:
            logger.warning("No images found to combine.")
            return None

        # Resize images to the desired resolution
        images = [img.resize((window_size[0], window_size[1])) for img in images]

        # Calculate grid size
        grid_rows, grid_columns = grid_size
        grid_width = grid_columns * window_size[0]
        grid_height = grid_rows * window_size[1]

        # Create the combined grid image
        grid_image = Image.new('RGB', (grid_width, grid_height), color=(255, 255, 255))

        for idx, img in enumerate(images):
            x = (idx % grid_columns) * window_size[0]
            y = (idx // grid_columns) * window_size[1]
            grid_image.paste(img, (x, y))

        # Rename combined image with timestamp
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        combined_image_name = f'combined_screenshots_{timestamp}.png'
        combined_image_path = os.path.join(screenshot_dir, combined_image_name)
        # Optimize image to reduce file size
        grid_image.save(combined_image_path, format='PNG', optimize=True)
        add_timestamp_to_image(combined_image_path)
        logger.info(f"Combined image saved: {combined_image_path}")
        return combined_image_path
    except Exception as e:
        logger.error(f"Failed to combine images into grid: {e}", exc_info=True)
        return None

def clean_temporary_files() -> None:
    """
    Clean up local temporary files.
    """
    try:
        shutil.rmtree(config.screenshot_dir, ignore_errors=True)
        os.makedirs(config.screenshot_dir, exist_ok=True)
        logger.info("Temporary files cleaned up.")
    except Exception as e:
        logger.error(f"Failed to clean temporary files: {e}", exc_info=True)

def handle_shutdown_signal(signum: int, frame: Any) -> None:
    """
    Handle shutdown signals to initiate graceful shutdown.

    Parameters:
        signum (int): Signal number.
        frame (frame object): Current stack frame.
    """
    global shutdown_signal_received
    logger.info(f"Received shutdown signal ({signum}). Initiating graceful shutdown...")
    shutdown_signal_received = True
    shutdown_event.set()
    resource_monitor_event.set()

# Register signal handlers
signal.signal(signal.SIGINT, handle_shutdown_signal)   # Handle Ctrl+C
signal.signal(signal.SIGTERM, handle_shutdown_signal)  # Handle termination signal

# Handle additional signals only if they are available on the platform
if hasattr(signal, 'SIGHUP'):
    try:
        signal.signal(signal.SIGHUP, handle_shutdown_signal)   # Handle hangup signal
    except (AttributeError, ValueError) as e:
        logger.warning(f"Unable to register SIGHUP handler: {e}")

if hasattr(signal, 'SIGQUIT'):
    try:
        signal.signal(signal.SIGQUIT, handle_shutdown_signal)  # Handle quit signal
    except (AttributeError, ValueError) as e:
        logger.warning(f"Unable to register SIGQUIT handler: {e}")

def process_site(driver: webdriver.Chrome, site: str, start_time: datetime) -> None:
    """
    Process a single website.

    Parameters:
        driver (WebDriver): Selenium WebDriver instance.
        site (str): URL of the website.
        start_time (datetime): Script start time.
    """
    if shutdown_event.is_set():
        logger.info(f"Shutdown event detected before processing {site}. Skipping.")
        return
    site_start_time = datetime.now()
    try:
        # Adjust timeout for specific slow website if needed
        success = load_website_with_retry(driver, site)
        if success:
            # Additional delay to ensure all content is loaded
            total_delay = 5 + 2  # Existing 5 seconds + extra 2 seconds
            logger.info(f"Waiting an additional {total_delay} seconds for {site} to load fully.")
            time.sleep(total_delay)
        status = "success" if success else "failed"
        screenshot_path = take_fullpage_screenshot(driver, site, status)
        if not success:
            raise Exception("Failed to load the page successfully.")
        successful_sites.append(site)
    except Exception as e:
        logger.error(f"Error processing {site}: {e}", exc_info=True)
        failed_sites[site] = str(e)
    finally:
        site_end_time = datetime.now()
        site_duration = site_end_time - site_start_time
        logger.info(f"Time taken for {site}: {site_duration}")
        if not shutdown_event.is_set():
            time.sleep(random.uniform(1, 3))

def load_website_with_retry(driver: webdriver.Chrome, site: str, timeout: int = 60) -> bool:
    """
    Attempt to load a website with retries.

    Parameters:
        driver (WebDriver): Selenium WebDriver instance.
        site (str): URL of the website.
        timeout (int): Timeout in seconds.

    Returns:
        bool: True if website loaded successfully, False otherwise.
    """
    try:
        driver.set_page_load_timeout(timeout)
        driver.get(site)
        if not wait_for_page_load(driver, timeout=timeout):
            return False
        return True
    except Exception as e:
        logger.error(f"Error loading website {site}: {e}", exc_info=True)
        return False

def wait_for_page_load(driver: webdriver.Chrome, timeout: int = 60) -> bool:
    """
    Wait for the page to load completely.

    Parameters:
        driver (WebDriver): Selenium WebDriver instance.
        timeout (int): Timeout in seconds.

    Returns:
        bool: True if page loaded, False otherwise.
    """
    try:
        # Wait for the document ready state to be 'complete'
        WebDriverWait(driver, timeout).until(
            lambda d: d.execute_script('return document.readyState') == 'complete' or shutdown_event.is_set()
        )
    except TimeoutException:
        logger.warning(f"Timeout waiting for page to load after {timeout} seconds.")
        return False
    return True

def take_fullpage_screenshot(driver: webdriver.Chrome, site_name: str, status: str) -> str:
    """
    Take a screenshot of the current page with metadata.

    Parameters:
        driver (WebDriver): Selenium WebDriver instance.
        site_name (str): URL of the site.
        status (str): Status of the processing ('success' or 'failed').

    Returns:
        str: Path to the saved screenshot.
    """
    if shutdown_event.is_set():
        logger.info("Shutdown event detected. Skipping screenshot.")
        raise Exception("Shutdown event detected.")
    try:
        site_name_clean = re.sub(r'[^A-Za-z0-9]', '_', site_name.replace("https://", "").replace("http://", ""))
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        screenshot_name = f"{site_name_clean}_{timestamp}_{status}.png"
        screenshot_path = os.path.join(config.screenshot_dir, screenshot_name)

        # Set window size to desired resolution
        driver.set_window_size(window_size[0], window_size[1])

        # Wait for page to load completely
        wait_for_page_load(driver)

        # Take screenshot of the viewport
        driver.save_screenshot(screenshot_path)
        add_timestamp_to_image(screenshot_path)
        logger.info(f"Screenshot saved: {screenshot_path}")
        return screenshot_path
    except Exception as e:
        logger.error(f"Failed to take screenshot for {site_name}: {e}", exc_info=True)
        raise e

def main() -> None:
    """
    Main function to execute the script.
    """
    global combined_image_path

    start_time = datetime.now()
    logger.info(f"Script started at {start_time}")

    # Record initial Disk I/O and Network I/O counters
    initial_disk_io = psutil.disk_io_counters()
    initial_net_io = psutil.net_io_counters()

    # Archive old screenshots before taking new ones
    archive_old_screenshots()

    # Start resource monitoring in a separate thread
    resource_thread = threading.Thread(target=monitor_resources)
    resource_thread.start()

    driver: Optional[webdriver.Chrome] = None  # Initialize driver variable
    error_occurred: bool = False  # Flag to indicate if any errors occurred
    error_details: Optional[str] = None

    try:
        driver = initialize_webdriver()

        # Process websites with progress bar
        for site in tqdm(websites, desc="Processing websites"):
            if shutdown_event.is_set():
                logger.info("Shutdown event detected. Stopping website processing.")
                break
            process_site(driver, site, start_time)

    except Exception as e:
        if shutdown_event.is_set():
            logger.info("Shutdown event detected during main execution.")
            error_details = "Script was interrupted by shutdown signal."
            error_occurred = True
        else:
            logger.error(f"An unexpected error occurred in main: {e}", exc_info=True)
            error_details = f"An unexpected error occurred: {e}"
            error_occurred = True
    finally:
        # Signal the resource monitor thread to stop
        resource_monitor_event.set()
        resource_thread.join()
        if driver:
            try:
                driver.quit()
            except Exception as e:
                logger.error(f"Failed to quit WebDriver: {e}", exc_info=True)

        end_time = datetime.now()
        total_time = end_time - start_time
        avg_cpu_usage = sum(cpu_usages) / len(cpu_usages) if cpu_usages else 0
        avg_ram_usage = sum(ram_usages) / len(ram_usages) if ram_usages else 0

        # Calculate total Disk I/O and Network I/O
        final_disk_io = psutil.disk_io_counters()
        final_net_io = psutil.net_io_counters()

        total_disk_read = final_disk_io.read_bytes - initial_disk_io.read_bytes
        total_disk_write = final_disk_io.write_bytes - initial_disk_io.write_bytes
        total_net_sent = final_net_io.bytes_sent - initial_net_io.bytes_sent
        total_net_recv = final_net_io.bytes_recv - initial_net_io.bytes_recv

        combined_image_url: Optional[str] = None

        if not shutdown_signal_received and not error_occurred:
            # Combine screenshots into a grid
            combined_image_path = combine_images_into_grid(config.screenshot_dir, grid_size=grid_size)

            if combined_image_path:
                # Upload the combined image to FTP
                try:
                    upload_success = send_with_retry(
                        func=upload_to_ftp,
                        file_path=combined_image_path,
                        exceptions=(Exception,),
                        total_tries=3,
                        initial_wait=2,
                        backoff_factor=2,
                    )
                    if upload_success:
                        # Construct the URL to access the image
                        combined_image_url = f"{base_url}{os.path.basename(combined_image_path)}"
                except Exception as e:
                    logger.error(f"Error during FTP upload: {e}", exc_info=True)
                    error_details = f"FTP upload failed: {e}"
                    error_occurred = True
            else:
                error_details = "Failed to create combined image."
                error_occurred = True
        elif error_occurred:
            # If an error occurred, ensure error_details is set
            if not error_details:
                error_details = "An unknown error occurred."

        # Send Pushover notification regardless of shutdown event
        send_pushover_notification(
            start_time,
            end_time,
            total_time,
            avg_cpu_usage,
            avg_ram_usage,
            combined_image_url,
            total_disk_read,
            total_disk_write,
            total_net_sent,
            total_net_recv,
            error_occurred=error_occurred,
            error_details=error_details
        )

        # Clean up temporary files
        clean_temporary_files()

        logger.info(f"Script completed at {end_time}, Total time: {total_time}")
        print(f"Total time taken: {total_time}")

# =============================================================================
# Entry Point
# =============================================================================

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        logger.info("KeyboardInterrupt received. Initiating graceful shutdown...")
        shutdown_signal_received = True
        shutdown_event.set()
        resource_monitor_event.set()
    except Exception as e:
        logger.error(f"An unhandled exception occurred: {e}", exc_info=True)
        shutdown_signal_received = True
        shutdown_event.set()
        resource_monitor_event.set()
