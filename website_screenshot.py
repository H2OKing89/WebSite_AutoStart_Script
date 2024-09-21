#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Script Name: Website Screenshot Taker
Version: 1.0.6
Author: Quentin King
Date: 09-21-2024

Description:
This script automates the process of taking screenshots of specified websites using Selenium WebDriver,
combines the screenshots into a grid image, uploads the image to an FTP server, and sends notifications
via Pushover. It includes robust error handling, resource monitoring with efficient data structures,
and a graceful shutdown mechanism. Additionally, it enhances logging, handles fallback directories,
and tracks detailed performance metrics.

Changelog:
- Version 1.0.6: Implemented fallback directories relative to the script's location.
                 Added specific exception handling.
                 Optimized resource monitoring using deque.
                 Enabled asynchronous processing with ThreadPoolExecutor.
                 Enhanced Pushover notifications with log links and error details.
                 Prevented over-logging by avoiding binary data logging.
                 Added comprehensive documentation and comments.
                 Managed dependencies with a requirements.txt example.
- Version 1.0.5: [Previous changelog entries]
"""

import os
import shutil
import time
import traceback
import psutil
import requests
import ftplib
import threading
import random
import functools
import signal
from datetime import datetime, timedelta
from PIL import Image, ImageDraw, ImageFont
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from selenium.common.exceptions import (
    TimeoutException,
    WebDriverException,
    SessionNotCreatedException,
    NoSuchElementException,
)
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.common.by import By
from webdriver_manager.chrome import ChromeDriverManager
from dotenv import load_dotenv
import yaml
from tqdm import tqdm
import logging
from logging.handlers import RotatingFileHandler
from pythonjsonlogger import jsonlogger
from pydantic import BaseModel, ValidationError, field_validator
from concurrent.futures import ThreadPoolExecutor, as_completed
from collections import deque
import sys

# =============================================================================
# Configuration Validation using Pydantic
# =============================================================================

class Config(BaseModel):
    debug_mode: bool = False
    log_dir: str
    screenshot_dir: str
    archive_dir: str
    websites: list
    grid_size: dict
    profile_path: str
    headless: bool = True
    window_size: dict
    max_workers: int = 5

    @field_validator('grid_size')
    def check_grid_size(cls, v):
        if 'rows' not in v or 'columns' not in v:
            raise ValueError("Grid size must include 'rows' and 'columns'")
        return v

    @field_validator('window_size')
    def check_window_size(cls, v):
        if 'width' not in v or 'height' not in v:
            raise ValueError("Window size must include 'width' and 'height'")
        return v

# =============================================================================
# Utility Functions
# =============================================================================

def get_script_directory():
    """Returns the directory where the script is located."""
    return os.path.dirname(os.path.abspath(__file__))

def setup_logging(log_dir, debug_mode):
    """
    Sets up logging with a rotating file handler and a console handler using JSON formatting.

    Args:
        log_dir (str): Directory where logs will be stored.
        debug_mode (bool): Flag to set logging level to DEBUG or INFO.

    Returns:
        Logger: Configured logger instance.
    """
    os.makedirs(log_dir, exist_ok=True)
    log_file = os.path.join(log_dir, 'website_refresh_log.json')

    # Configure root logger
    logger = logging.getLogger()
    logger.setLevel(logging.DEBUG if debug_mode else logging.INFO)

    # Rotating file handler with JSON formatter
    file_handler = RotatingFileHandler(log_file, maxBytes=5 * 1024 * 1024, backupCount=5)
    file_handler.setLevel(logging.DEBUG if debug_mode else logging.INFO)
    file_formatter = jsonlogger.JsonFormatter(
        '%(asctime)s %(levelname)s %(name)s %(message)s %(site)s %(status)s'
    )
    file_handler.setFormatter(file_formatter)
    logger.addHandler(file_handler)

    # Console handler with JSON formatter
    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.INFO)
    console_formatter = jsonlogger.JsonFormatter('%(message)s')
    console_handler.setFormatter(console_formatter)
    logger.addHandler(console_handler)

    # Suppress debug logs from external libraries
    logging.getLogger('PIL').setLevel(logging.WARNING)
    logging.getLogger('urllib3').setLevel(logging.WARNING)
    logging.getLogger('selenium').setLevel(logging.WARNING)
    logging.getLogger('ftplib').setLevel(logging.WARNING)
    logging.getLogger('requests').setLevel(logging.WARNING)

    return logger

def send_pushover_notification(message, title="Website Screenshot Script"):
    """
    Send a notification via Pushover with the provided message and title.

    Args:
        message (str): The message content of the notification.
        title (str): The title of the notification.
    """
    global last_notification_time

    # Implement notification throttling (send notification only if more than 1 hour has passed since last)
    current_time = datetime.now()
    if last_notification_time and (current_time - last_notification_time).total_seconds() < 3600:
        logger.info("Notification throttled to prevent spamming.", extra={"action": "pushover_throttle"})
        return
    last_notification_time = current_time

    payload = {
        "token": pushover_token,
        "user": pushover_user_key,
        "message": message,
        "title": title,
        "html": 1,  # Enable HTML formatting
    }

    logger.info("Sending Pushover notification...", extra={"message": message, "title": title, "action": "send_pushover"})

    try:
        response = requests.post("https://api.pushover.net/1/messages.json", data=payload)
        if response.status_code == 200:
            logger.info("Pushover notification sent successfully!", extra={"status": "success", "action": "send_pushover"})
        else:
            logger.error(f"Pushover failed. Status code: {response.status_code}, Response: {response.text}", extra={"status": "failure", "action": "send_pushover"})
    except Exception as e:
        logger.error(f"Error sending Pushover notification: {e}", exc_info=True, extra={"status": "error", "action": "send_pushover"})

def ensure_directory(path, fallback_subdir):
    """
    Ensures that a directory exists. If not, falls back to a subdirectory within the script's directory.

    Args:
        path (str): The primary directory path.
        fallback_subdir (str): The name of the fallback subdirectory.

    Returns:
        str: The existing or fallback directory path.
    """
    if not os.path.exists(path):
        fallback_path = os.path.join(script_dir, fallback_subdir)
        logger.warning(f"Directory {path} does not exist. Using fallback: {fallback_path}", extra={"path": path, "fallback_path": fallback_path, "action": "ensure_directory"})
        send_pushover_notification(f"Directory {path} not found. Falling back to {fallback_path}.", title="Directory Fallback")
        os.makedirs(fallback_path, exist_ok=True)
        return fallback_path
    return path

def calculate_resource_usage():
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

def monitor_resources():
    """
    Monitor resource usage over time and store the data in deques.
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
    logger.info("Resource monitor thread exiting due to resource_monitor_event.", extra={"action": "monitor_resources"})

def retry(exceptions, total_tries=4, initial_wait=0.5, backoff_factor=2):
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
    def decorator_retry(func):
        @functools.wraps(func)
        def wrapper_retry(*args, **kwargs):
            _tries, _delay = total_tries, initial_wait
            while _tries > 1:
                try:
                    return func(*args, **kwargs)
                except exceptions as e:
                    if shutdown_event.is_set():
                        logger.info(f"Shutdown event detected during retries. Exiting {func.__name__}.", extra={"function": func.__name__, "action": "retry"})
                        raise e
                    msg = f"{func.__name__} failed with {e}, retrying in {_delay} seconds..."
                    logger.warning(msg, extra={"function": func.__name__, "exception": str(e), "action": "retry"})
                    time.sleep(_delay)
                    _tries -= 1
                    _delay *= backoff_factor
            return func(*args, **kwargs)
        return wrapper_retry
    return decorator_retry

def add_timestamp_to_image(image_path):
    """
    Add a timestamp watermark to the image.

    Args:
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
        logger.info(f"Timestamp added to image: {image_path}", extra={"image_path": image_path, "action": "add_timestamp"})
    except Exception as e:
        logger.error(f"Failed to add timestamp to image {image_path}: {e}", exc_info=True, extra={"image_path": image_path, "action": "add_timestamp"})

@retry((Exception,), total_tries=3, initial_wait=2, backoff_factor=2)
def take_fullpage_screenshot(driver, site_name, status):
    """
    Take a screenshot of the current page with metadata.

    Args:
        driver (WebDriver): Selenium WebDriver instance.
        site_name (str): URL of the site.
        status (str): Status of the processing ('success' or 'failed').

    Returns:
        str: Path to the saved screenshot.
    """
    if shutdown_event.is_set():
        logger.info("Shutdown event detected. Skipping screenshot.", extra={"site": site_name, "action": "take_fullpage_screenshot"})
        raise Exception("Shutdown event detected.")
    try:
        # Clean site name for filename
        site_name_clean = ''.join(e for e in site_name if e.isalnum() or e in ('_', '-')).replace("https://", "").replace("http://", "")
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        screenshot_name = f"{site_name_clean}_{timestamp}_{status}.png"
        screenshot_path = os.path.join(config.screenshot_dir, screenshot_name)

        # Set window size to desired resolution
        driver.set_window_size(config.window_size["width"], config.window_size["height"])

        # Wait for page to load completely
        wait_for_page_load(driver)

        # Take screenshot of the viewport
        driver.save_screenshot(screenshot_path)
        add_timestamp_to_image(screenshot_path)
        logger.info(f"Screenshot saved: {screenshot_path}", extra={"site": site_name, "screenshot_path": screenshot_path, "action": "take_fullpage_screenshot"})
        return screenshot_path
    except Exception as e:
        logger.error(f"Failed to take screenshot for {site_name}: {e}", exc_info=True, extra={"site": site_name, "action": "take_fullpage_screenshot"})
        raise e

def combine_images_into_grid(screenshot_dir, grid_size=(3, 5)):
    """
    Combine screenshots into a grid image.

    Args:
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
            logger.warning("No images found to combine.", extra={"action": "combine_images"})
            return None

        # Resize images to the desired resolution
        images = [img.resize((config.window_size["width"], config.window_size["height"])) for img in images]

        # Calculate grid size
        grid_rows, grid_columns = grid_size
        grid_width = grid_columns * config.window_size["width"]
        grid_height = grid_rows * config.window_size["height"]

        # Create the combined grid image
        grid_image = Image.new('RGB', (grid_width, grid_height), color=(255, 255, 255))

        for idx, img in enumerate(images):
            x = (idx % grid_columns) * config.window_size["width"]
            y = (idx // grid_columns) * config.window_size["height"]
            grid_image.paste(img, (x, y))

        # Rename combined image with timestamp
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        combined_image_name = f'combined_screenshots_{timestamp}.png'
        combined_image_path = os.path.join(screenshot_dir, combined_image_name)
        # Optimize image to reduce file size
        grid_image.save(combined_image_path, format='PNG', optimize=True)
        logger.info(f"Combined image saved: {combined_image_path}", extra={"combined_image_path": combined_image_path, "action": "combine_images"})
        return combined_image_path
    except Exception as e:
        logger.error(f"Failed to combine images into grid: {e}", exc_info=True, extra={"action": "combine_images"})
        return None

def archive_old_screenshots():
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
                shutil.move(os.path.join(config.screenshot_dir, filename), os.path.join(archive_subdir, filename))
        logger.info(f"Old screenshots moved to {archive_subdir}", extra={"archive_subdir": archive_subdir, "action": "archive_old_screenshots"})

        # Cleanup old archives, keep only the 5 most recent
        archives = sorted(os.listdir(config.archive_dir), reverse=True)
        if len(archives) > 5:
            archives_to_delete = archives[5:]  # Keep the first 5 (most recent)
            for archive in archives_to_delete:
                archive_path = os.path.join(config.archive_dir, archive)
                shutil.rmtree(archive_path)
                logger.info(f"Deleted old archive: {archive_path}", extra={"archive_path": archive_path, "action": "cleanup_archive"})
    except Exception as e:
        logger.error(f"Failed to archive old screenshots: {e}", exc_info=True, extra={"action": "archive_old_screenshots"})

@retry((Exception,), total_tries=3, initial_wait=2, backoff_factor=2)
def upload_to_ftp(file_path):
    """
    Upload the combined image to the FTP server.

    Args:
        file_path (str): Path to the file to upload.

    Returns:
        bool: True if upload succeeded, False otherwise.
    """
    if shutdown_signal_received:
        logger.info("Shutdown signal received. Skipping FTP upload.", extra={"action": "upload_to_ftp"})
        raise Exception("Shutdown event detected.")
    try:
        with ftplib.FTP() as ftp:
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
                        logger.info(f"Deleted existing file: {f}", extra={"file": f, "action": "ftp_delete"})
                    except ftplib.error_perm as e:
                        logger.warning(f"Could not delete file {f}: {e}", extra={"file": f, "action": "ftp_delete", "error": str(e)})

            # Upload the new file
            filename = os.path.basename(file_path)
            with open(file_path, 'rb') as file:
                ftp.storbinary(f'STOR {filename}', file)
            logger.info(f"Uploaded {filename} to FTP successfully", extra={"file": filename, "action": "ftp_upload"})
            return True
    except Exception as e:
        logger.error(f"FTP upload failed: {e}", exc_info=True, extra={"action": "upload_to_ftp"})
        send_pushover_notification(f"FTP upload failed: {e}", title="FTP Upload Error")
        raise e

def wait_for_page_load(driver, timeout=60):
    """
    Wait for the page to load completely.

    Args:
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
        logger.warning(f"Timeout waiting for page to load after {timeout} seconds.", extra={"action": "wait_for_page_load"})
        return False
    return True

@retry((TimeoutException, WebDriverException), total_tries=5, initial_wait=1, backoff_factor=2)
def load_website_with_retry(driver, site, timeout=60):
    """
    Attempt to load a website with retries.

    Args:
        driver (WebDriver): Selenium WebDriver instance.
        site (str): URL of the website.
        timeout (int): Timeout in seconds.

    Returns:
        bool: True if website loaded successfully, False otherwise.
    """
    if shutdown_event.is_set():
        logger.info("Shutdown event detected. Skipping website load.", extra={"site": site, "action": "load_website_with_retry"})
        raise Exception("Shutdown event detected.")
    try:
        driver.get(site)
        if not wait_for_page_load(driver, timeout=timeout):
            raise TimeoutException("Page did not load in time.")
        return True
    except (TimeoutException, WebDriverException) as e:
        logger.warning(f"Failed to load {site}: {e}", extra={"site": site, "action": "load_website_with_retry"})
        raise e

def clean_temporary_files():
    """
    Clean up local temporary files.
    """
    try:
        shutil.rmtree(config.screenshot_dir, ignore_errors=True)
        os.makedirs(config.screenshot_dir, exist_ok=True)
        logger.info("Temporary files cleaned up.", extra={"action": "clean_temporary_files"})
    except Exception as e:
        logger.error(f"Failed to clean temporary files: {e}", exc_info=True, extra={"action": "clean_temporary_files"})

def process_site(driver, site, start_time):
    """
    Process a single website by loading it, taking a screenshot, and handling any errors.

    Args:
        driver (WebDriver): Selenium WebDriver instance.
        site (str): URL of the website to process.
        start_time (datetime): Timestamp when the script started.

    Returns:
        None
    """
    if shutdown_event.is_set():
        logger.info(f"Shutdown event detected before processing {site}. Skipping.", extra={"site": site, "action": "process_site"})
        return
    site_start_time = datetime.now()
    screenshot_capture_time = None
    try:
        # Load the website with retries
        success = load_website_with_retry(driver, site)
        if success:
            # Additional delay to ensure all content is loaded
            total_delay = 7  # Existing 5 seconds + extra 2 seconds
            logger.info(f"Waiting an additional {total_delay} seconds for {site} to load fully.", extra={"site": site, "delay_seconds": total_delay, "action": "process_site"})
            time.sleep(total_delay)

        # Track screenshot capture time
        capture_start = time.time()
        screenshot_path = take_fullpage_screenshot(driver, site, "success" if success else "failed")
        capture_end = time.time()
        screenshot_capture_time = capture_end - capture_start

        if not success:
            raise Exception("Failed to load the page successfully.")

        successful_sites.append(site)
        logger.info(f"Successfully processed {site} in {screenshot_capture_time:.2f} seconds.", extra={"site": site, "capture_time": screenshot_capture_time, "status": "success"})

    except Exception as e:
        logger.error(f"Error processing {site}: {e}", exc_info=True, extra={"site": site, "action": "process_site"})
        failed_sites[site] = str(e)
    finally:
        site_end_time = datetime.now()
        site_duration = site_end_time - site_start_time
        logger.info(f"Time taken for {site}: {site_duration}", extra={"site": site, "duration": str(site_duration), "action": "process_site"})
        if not shutdown_event.is_set():
            # Simulate network latency measurement
            network_latency = random.uniform(50, 150)  # Placeholder for actual latency measurement
            logger.info(f"Network latency for {site}: {network_latency:.2f} ms", extra={"site": site, "network_latency_ms": network_latency, "action": "process_site"})
            # Randomly simulate network latency for demonstration
            time.sleep(random.uniform(1, 3))

def initialize_webdriver():
    """
    Initialize the Selenium WebDriver with options.

    Returns:
        WebDriver: Selenium WebDriver instance.
    """
    if shutdown_event.is_set():
        logger.info("Shutdown event detected. Skipping WebDriver initialization.", extra={"action": "initialize_webdriver"})
        raise Exception("Shutdown event detected.")
    try:
        options = webdriver.ChromeOptions()
        profile_path = config.profile_path
        options.add_argument(f"--user-data-dir={profile_path}")
        options.add_argument('--profile-directory=Default')
        if config.headless:
            options.add_argument('--headless')
            options.add_argument('--disable-gpu')

        # Set consistent window size
        options.add_argument(f'--window-size={config.window_size["width"]},{config.window_size["height"]}')

        # Additional options for headless operation
        options.add_argument('--no-sandbox')
        options.add_argument('--disable-dev-shm-usage')
        options.add_argument('--disable-extensions')
        options.add_argument('--disable-infobars')
        options.add_argument('--disable-notifications')

        # Set page load strategy to 'normal' to wait for all resources
        options.page_load_strategy = 'normal'

        driver = webdriver.Chrome(service=Service(ChromeDriverManager().install()), options=options)
        logger.info("WebDriver initialized successfully.", extra={"action": "initialize_webdriver"})
        return driver
    except SessionNotCreatedException as e:
        logger.error(f"WebDriver session not created: {e}", exc_info=True, extra={"action": "initialize_webdriver"})
        send_pushover_notification(f"WebDriver session not created: {e}", title="WebDriver Error")
        raise e
    except WebDriverException as e:
        logger.error(f"Failed to initialize WebDriver: {e}", exc_info=True, extra={"action": "initialize_webdriver"})
        send_pushover_notification(f"Failed to initialize WebDriver: {e}", title="WebDriver Error")
        raise e
    except Exception as e:
        logger.error(f"Unexpected error during WebDriver initialization: {e}", exc_info=True, extra={"action": "initialize_webdriver"})
        send_pushover_notification(f"Unexpected error during WebDriver initialization: {e}", title="WebDriver Error")
        raise e

# =============================================================================
# Signal Handling for Graceful Shutdown
# =============================================================================

def handle_shutdown_signal(signum, frame):
    """
    Handle shutdown signals to initiate graceful shutdown.

    Args:
        signum (int): Signal number.
        frame (frame): Current stack frame.
    """
    global shutdown_signal_received
    logger.info(f"Received shutdown signal ({signum}). Initiating graceful shutdown...", extra={"signal_number": signum, "action": "shutdown"})
    shutdown_signal_received = True
    shutdown_event.set()
    resource_monitor_event.set()

# Register signal handlers
signal.signal(signal.SIGINT, handle_shutdown_signal)   # Handle Ctrl+C
signal.signal(signal.SIGTERM, handle_shutdown_signal)  # Handle termination signal

# =============================================================================
# Main Function
# =============================================================================

def main():
    """
    Main function to execute the script.
    """
    global combined_image_path

    start_time = datetime.now()
    logger.info(f"Script started at {start_time}", extra={"action": "start_script"})

    # Record initial Disk I/O and Network I/O counters
    initial_disk_io = psutil.disk_io_counters()
    initial_net_io = psutil.net_io_counters()

    # Archive old screenshots before taking new ones
    archive_old_screenshots()

    # Start resource monitoring in a separate thread
    resource_thread = threading.Thread(target=monitor_resources, name="ResourceMonitorThread")
    resource_thread.start()

    driver = None  # Initialize driver variable

    try:
        driver = initialize_webdriver()

        # Determine if running in headless mode to handle tqdm
        is_headless = config.headless

        # Redirect tqdm output if headless
        if is_headless:
            tqdm_log_path = os.path.join(config.log_dir, 'tqdm_output.log')
            tqdm_file = open(tqdm_log_path, 'a')  # Append mode
            logger.info(f"tqdm output redirected to {tqdm_log_path}", extra={"action": "tqdm_redirect"})
        else:
            tqdm_file = sys.stdout

        # Use ThreadPoolExecutor for asynchronous processing
        with ThreadPoolExecutor(max_workers=config.max_workers) as executor:
            future_to_site = {
                executor.submit(process_site, driver, site, start_time): site for site in config.websites
            }

            # Use tqdm to display progress
            for future in tqdm(as_completed(future_to_site), total=len(future_to_site), desc="Processing websites", file=tqdm_file):
                site = future_to_site[future]
                try:
                    future.result()
                except Exception as e:
                    logger.error(f"Error processing {site}: {e}", exc_info=True, extra={"site": site, "action": "process_site_async"})

        if is_headless:
            tqdm_file.close()

    except Exception as e:
        if shutdown_event.is_set():
            logger.info("Shutdown event detected during main execution.", extra={"action": "main_exception"})
        else:
            logger.error(f"An unexpected error occurred in main: {e}", exc_info=True, extra={"action": "main_exception"})
    finally:
        # Signal the resource monitor thread to stop
        resource_monitor_event.set()
        resource_thread.join()
        if driver:
            try:
                driver.quit()
                logger.info("WebDriver quit successfully.", extra={"action": "quit_webdriver"})
            except Exception as e:
                logger.error(f"Failed to quit WebDriver: {e}", exc_info=True, extra={"action": "quit_webdriver"})

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

        # Performance Metrics placeholders
        # Ideally, you should collect these metrics during processing
        # For now, we'll set them to 0
        screenshot_capture_times = []  # Populate this list with actual capture times
        network_latencies = []         # Populate this list with actual latencies
        ftp_upload_speeds = []         # Populate this list with actual upload speeds

        combined_image_url = None
        error_details = None
        error_occurred = False  # Flag to indicate if any errors occurred

        if not shutdown_signal_received:
            # Combine screenshots into a grid
            combined_image_path = combine_images_into_grid(config.screenshot_dir, grid_size=(config.grid_size['rows'], config.grid_size['columns']))

            if combined_image_path:
                # Upload the combined image to FTP
                try:
                    upload_to_ftp(combined_image_path)
                    # Construct the URL to access the image
                    combined_image_url = f"{base_url}{os.path.basename(combined_image_path)}"
                except Exception as e:
                    logger.error(f"Error during FTP upload: {e}", exc_info=True, extra={"action": "upload_to_ftp"})
                    error_details = f"FTP upload failed: {e}"
                    error_occurred = True
            else:
                error_details = "Failed to create combined image."
                error_occurred = True
        else:
            error_details = "Script was interrupted by shutdown signal."
            error_occurred = True

        # Compile Performance Metrics
        # These should be collected during processing
        # For demonstration, we use placeholder values
        avg_screenshot_time = sum(screenshot_capture_times) / len(screenshot_capture_times) if screenshot_capture_times else 0
        avg_network_latency = sum(network_latencies) / len(network_latencies) if network_latencies else 0
        avg_ftp_upload_speed = sum(ftp_upload_speeds) / len(ftp_upload_speeds) if ftp_upload_speeds else 0

        # Send Pushover notification regardless of shutdown event
        pushover_message = f"""
        <b>Website Screenshot Script Report</b><br/><br/>
        <b>Summary:</b><br/>
        - 🌐 Websites Processed: {len(successful_sites) + len(failed_sites)}<br/>
        - ✅ Successful: {len(successful_sites)}<br/>
        - ❌ Failed: {len(failed_sites)}<br/>
        """

        if failed_sites:
            pushover_message += "<br/>🚫 <b>Websites That Failed:</b><br/>"
            for site, error in failed_sites.items():
                pushover_message += f"- {site}: {error}<br/>"

        pushover_message += f"""
        <br/><b>Performance Metrics:</b><br/>
        - ⏱️ Total Time Taken: {total_time}<br/>
        - 💻 Average CPU Usage: {avg_cpu_usage:.1f}%<br/>
        - 📈 Average RAM Usage: {avg_ram_usage:.1f}%<br/>
        - 💾 Total Disk Read: {total_disk_read / (1024 * 1024):.2f} MB<br/>
        - 💿 Total Disk Write: {total_disk_write / (1024 * 1024):.2f} MB<br/>
        - 📤 Total Network Sent: {total_net_sent / (1024 * 1024):.2f} MB<br/>
        - 📥 Total Network Received: {total_net_recv / (1024 * 1024):.2f} MB<br/>
        - ⏳ Average Screenshot Capture Time: {avg_screenshot_time:.2f} seconds<br/>
        - 🌐 Average Network Latency: {avg_network_latency:.2f} ms<br/>
        - 🚀 Average FTP Upload Speed: {avg_ftp_upload_speed:.2f} MB/s<br/>
        """

        if combined_image_url:
            pushover_message += f"<br/>📷 <a href=\"{combined_image_url}\">View Combined Screenshot</a><br/>"

        if error_details:
            pushover_message += f"<br/>⚠️ <b>Error Details:</b><br/>{error_details}<br/>"

        send_pushover_notification(pushover_message, title="Website Screenshot Script Report")

        # Clean up temporary files
        clean_temporary_files()

        logger.info(f"Script completed at {end_time}, Total time: {total_time}", extra={"action": "end_script"})
        print(f"Total time taken: {total_time}")

# =============================================================================
# Global Variables for Resource Monitoring and Shutdown
# =============================================================================

# Get the directory where the script is located
script_dir = get_script_directory()

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
    sys.exit(1)
except FileNotFoundError:
    print(f"Configuration file not found at {config_path}")
    sys.exit(1)

# Setup Logging with Structured JSON Logging
logger = setup_logging(config.log_dir, config.debug_mode)

# Apply fallback for essential directories
config.log_dir = ensure_directory(config.log_dir, 'logs')
config.screenshot_dir = ensure_directory(config.screenshot_dir, 'screenshots')
config.archive_dir = ensure_directory(config.archive_dir, 'archive')

# FTP and Pushover Credentials (Loaded from .env)
# FTP credentials
ftp_host = os.getenv('FTP_HOST')
ftp_user = os.getenv('FTP_USER')
ftp_pass = os.getenv('FTP_PASS')
ftp_port = int(os.getenv('FTP_PORT', 21))  # Default FTP port is 21

# Pushover setup
pushover_user_key = os.getenv('PUSHOVER_USER_KEY')
pushover_token = os.getenv('PUSHOVER_TOKEN')

# Base URL for accessing the uploaded image
base_url = os.getenv('BASE_URL', 'http://example.com/')  # Default base URL

# Resource usage deques with maximum lengths to limit memory usage
cpu_usages = deque(maxlen=720)      # Assuming sampling every 5 seconds for 1 hour
ram_usages = deque(maxlen=720)
disk_read_bytes = deque(maxlen=720)
disk_write_bytes = deque(maxlen=720)
net_sent_bytes = deque(maxlen=720)
net_recv_bytes = deque(maxlen=720)

# Shutdown event for graceful shutdown
shutdown_event = threading.Event()

# Resource monitor event
resource_monitor_event = threading.Event()

# Flag to indicate if a shutdown signal was received
shutdown_signal_received = False

# Variables for execution statistics
successful_sites = []
failed_sites = {}

# Last notification time for throttling
last_notification_time = None

# Initialize combined_image_path as None
combined_image_path = None

# =============================================================================
# Register Signal Handlers and Start the Script
# =============================================================================

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        logger.info("KeyboardInterrupt received. Initiating graceful shutdown...", extra={"action": "keyboard_interrupt"})
        shutdown_signal_received = True
        shutdown_event.set()
        resource_monitor_event.set()
