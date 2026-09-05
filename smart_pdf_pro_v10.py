"""
Smart PDF Pro v4.5 - single-file desktop PDF toolkit (22 tools)
Full iLovePDF feature parity + Indian-language translation & OCR

Recommended installation (Windows/macOS/Linux):
    python -m pip install pypdf pymupdf pillow pdf2docx pdfplumber openpyxl xlsxwriter \
        python-docx python-pptx reportlab pytesseract cryptography \
        "pyHanko[image-support,opentype]" pyhanko-certvalidator \
        deep-translator langdetect pymupdf4llm argostranslate

OFFLINE TRANSLATION (Argos Translate):
    Translate PDF now has an "Offline" engine that runs entirely on this PC once its
    language packs are installed — no text ever leaves the machine.
    - One-time setup per language pair: open Translate PDF, choose "Offline", pick the
      From/To languages, and click "Download language pack" (requires internet once).
    - After that, translation for that language pair works with no internet connection.
    - Offline coverage today: English, Hindi, Bengali, Urdu, Arabic, Chinese, Japanese,
      French, German, Spanish. Marathi, Gujarati, Tamil, Telugu, Kannada, Malayalam,
      Punjabi, Odia, Assamese, Sanskrit and Nepali are not yet available from Argos
      Translate and still require the "Online" engine (Google Translate / MyMemory).

TESSERACT OCR (only needed for scanned/image PDFs):
    Windows: https://github.com/UB-Mannheim/tesseract/wiki
    - During install, tick "Additional language data" and select Hindi (hin),
      Gujarati (guj), Marathi (mar) or whichever languages you need.
    - After install, use the "Locate Tesseract" button in the Translate screen
      to point to tesseract.exe if it is not found automatically.
    NOTE: Selectable-text PDFs do NOT need Tesseract at all.

LibreOffice (optional):
    Preferred for Word/Excel → PDF when MS Office is unavailable.

Run:
    python smart_pdf_pro_v4.py
"""

from __future__ import annotations

import io
import json
import hashlib
import hmac
import secrets
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import traceback
import uuid
from dataclasses import dataclass
from datetime import date, datetime, timedelta, timezone
from html import escape as html_escape
from html.parser import HTMLParser
from pathlib import Path
from typing import Callable, Iterable, Optional, Sequence
from urllib.error import HTTPError, URLError
from urllib.parse import unquote, urljoin, urlparse
from urllib.request import Request, urlopen

import tkinter as tk
from tkinter import filedialog, messagebox, ttk


APP_NAME = "Smart PDF Pro"
APP_SUBTITLE = "Professional PDF tools by Taxosmart"
MAX_FILE_BYTES = 500 * 1024 * 1024

COLORS = {
    # ── Blue scale (single hue, varying lightness) ──
    "blue_900":     "#12263F",   # deepest — headings, sidebar text
    "blue_800":     "#1B3A5C",   # dark
    "blue_700":     "#22527E",   # sidebar active / primary buttons
    "blue_600":     "#2C6BA0",   # primary hover
    "blue_500":     "#4A87BD",   # mid — icons, accents
    "blue_300":     "#93B6D6",   # light — borders on blue
    "blue_200":     "#C3D8EC",   # very light — dividers
    "blue_100":     "#E1EBF5",   # tint — section strips
    "blue_050":     "#F2F7FC",   # faintest — input fields, hover

    # ── White scale ──
    "white":        "#FFFFFF",
    "off_white":    "#FAFCFE",

    # ── Semantic roles (all mapped into the blue/white scale) ──
    "sidebar":      "#FFFFFF",   # white sidebar
    "sidebar_2":    "#F2F7FC",   # sidebar hover
    "accent":       "#22527E",   # primary action
    "accent_dark":  "#12263F",   # primary pressed
    "ink":          "#12263F",   # body text
    "paper":        "#FAFCFE",   # page background
    "panel":        "#FFFFFF",   # card background
    "soft":         "#F2F7FC",   # header strip / section background
    "line":         "#C3D8EC",   # borders
    "muted":        "#5E7A96",   # secondary text

    # ── Status (kept within the blue family, differentiated by weight) ──
    "success":      "#16A34A",
    "danger":       "#DC2626",
    "warning":      "#EA580C",
    "green":        "#16A34A",
    "green_dark":   "#15803D",
    "orange":       "#F97316",
    "orange_dark":  "#C2410C",
    "red":          "#DC2626",
    "red_dark":     "#B91C1C",
    "violet":       "#7C3AED",
    "violet_dark":  "#5B21B6",

    # ── Category aliases used by feature cards (all one blue now) ──
    "blue":         "#22527E",
    "purple":       "#22527E",
    "teal":         "#22527E",
    "gold":         "#22527E",
    "sage":         "#22527E",
    "rust":         "#22527E",
    "rust_dark":    "#12263F",
}

LANGUAGES = {
    "Auto detect": "auto",
    "English": "en",
    "Hindi / हिन्दी": "hi",
    "Marathi / मराठी": "mr",
    "Gujarati / ગુજરાતી": "gu",
    "Bengali / বাংলা": "bn",
    "Tamil / தமிழ்": "ta",
    "Telugu / తెలుగు": "te",
    "Kannada / ಕನ್ನಡ": "kn",
    "Malayalam / മലയാളം": "ml",
    "Punjabi / ਪੰਜਾਬੀ": "pa",
    "Urdu / اردو": "ur",
    "Assamese / অসমীয়া": "as",
    "Odia / ଓଡ଼ିଆ": "or",
    "Sanskrit / संस्कृतम्": "sa",
    "Nepali / नेपाली": "ne",
    "Arabic / العربية": "ar",
    "French / Français": "fr",
    "German / Deutsch": "de",
    "Spanish / Español": "es",
    "Chinese (Simplified) / 中文": "zh-CN",
    "Japanese / 日本語": "ja",
}

TESSERACT_LANGUAGES = {
    "en": "eng", "hi": "hin", "mr": "mar", "gu": "guj", "bn": "ben",
    "ta": "tam", "te": "tel", "kn": "kan", "ml": "mal", "pa": "pan",
    "ur": "urd", "as": "asm", "or": "ori", "sa": "san", "ne": "nep",
    "ar": "ara", "fr": "fra", "de": "deu", "es": "spa", "ja": "jpn",
    "zh-CN": "chi_sim",
}

MYMEMORY_LANGUAGES = {
    "en": "en-GB", "hi": "hi-IN", "mr": "mr-IN", "gu": "gu-IN",
    "bn": "bn-IN", "ta": "ta-IN", "te": "te-IN", "kn": "kn-IN",
    "ml": "ml-IN", "pa": "pa-IN", "ur": "ur-PK", "as": "as-IN",
    "or": "or-IN", "sa": "sa-IN", "ne": "ne-NP", "ar": "ar-SA",
    "fr": "fr-FR", "de": "de-DE", "es": "es-ES", "zh-CN": "zh-CN",
    "ja": "ja-JP",
}


class FeatureError(RuntimeError):
    """A concise, user-facing feature error."""


def need(module: str, package: Optional[str] = None):
    """Import a feature dependency and provide a useful installation message."""
    try:
        return __import__(module)
    except ImportError as exc:
        install_name = package or module
        raise FeatureError(
            f"This feature requires '{install_name}'.\n\n"
            f"Install it with:\n{sys.executable} -m pip install {install_name}"
        ) from exc


def get_pymupdf():
    # Do not use the deprecated `fitz` compatibility import.
    return need("pymupdf")


def check_size(path: str | Path) -> None:
    size = Path(path).stat().st_size
    if size > MAX_FILE_BYTES:
        raise FeatureError(f"{Path(path).name} exceeds the 500 MB limit.")


def require_distinct_output(output: str | Path, inputs: Iterable[str | Path]) -> None:
    destination = Path(output).resolve()
    for source in inputs:
        if destination == Path(source).resolve():
            raise FeatureError(
                "The output must have a different filename from the source file."
            )


def safe_filename(name: str, fallback: str = "output") -> str:
    clean = re.sub(r"[^\w\-.() ]+", "", name, flags=re.UNICODE).strip(" .")
    return clean or fallback


def unique_path(path: str | Path) -> Path:
    path = Path(path)
    if not path.exists():
        return path
    for number in range(1, 10000):
        candidate = path.with_name(f"{path.stem}_{number}{path.suffix}")
        if not candidate.exists():
            return candidate
    raise FeatureError(f"Could not create a unique output name for {path.name}.")


def human_size(size: int) -> str:
    value = float(size)
    for unit in ("B", "KB", "MB", "GB"):
        if value < 1024 or unit == "GB":
            return f"{value:.0f} {unit}" if unit == "B" else f"{value:.2f} {unit}"
        value /= 1024
    return f"{size} B"


def parse_pages(text: str, total: int) -> list[int]:
    """Parse '1-3,5,8-10' into sorted unique zero-based page indices."""
    if total < 1:
        return []
    if not text.strip():
        return list(range(total))
    result: set[int] = set()
    for raw in text.split(","):
        part = raw.strip()
        if not part:
            continue
        if "-" in part:
            bits = part.split("-")
            if len(bits) != 2:
                raise FeatureError(f"Invalid page range: {part}")
            try:
                start, end = (int(bits[0].strip()), int(bits[1].strip()))
            except ValueError as exc:
                raise FeatureError(f"Invalid page range: {part}") from exc
            if start < 1 or end < start or end > total:
                raise FeatureError(f"Page range {part} must be within 1-{total}.")
            result.update(range(start - 1, end))
        else:
            try:
                page = int(part)
            except ValueError as exc:
                raise FeatureError(f"Invalid page number: {part}") from exc
            if page < 1 or page > total:
                raise FeatureError(f"Page {page} must be within 1-{total}.")
            result.add(page - 1)
    if not result:
        raise FeatureError("Enter at least one valid page or range.")
    return sorted(result)


def parse_groups(text: str, total: int) -> list[list[int]]:
    """Parse semicolon-separated PDF groups, e.g. '1-3; 4,6; 5,7-9'."""
    groups = []
    for part in text.split(";"):
        if part.strip():
            groups.append(parse_pages(part, total))
    if not groups:
        raise FeatureError("Enter at least one page group, separated with semicolons.")
    return groups


def open_in_file_manager(path: str | Path) -> None:
    target = str(Path(path).resolve())
    try:
        if sys.platform.startswith("win"):
            os.startfile(target)  # type: ignore[attr-defined]
        elif sys.platform == "darwin":
            subprocess.Popen(["open", target])
        else:
            subprocess.Popen(["xdg-open", target])
    except Exception as exc:
        raise FeatureError(f"Could not open the location: {exc}") from exc


# ---------------------------------------------------------------------------
# Embedded brand assets (base64 PNG) — keeps this a single-file application
# ---------------------------------------------------------------------------

LOGO_LEFT_B64 = (
    "iVBORw0KGgoAAAANSUhEUgAAAL4AAAAsCAYAAADb2gLVAAA0NklEQVR42u2dd5wdVfn/3+ecmbl1+2Y32fQEQkIgCRAiEekEBEHw"
    "Kyp2v4qIBez1p7zULyqoYBcLNkQERBBRkB5qKAmEhBRSN5vdzWb77u0zc875/TGzm90UiF/x9W1OXvPamzv3TjnnOU/5PJ/nucJa"
    "a/k7NwsI/rX9a/ufuzkHK+gWi7QhxoCUDtZoDBolwMoEYOPF8K8l8a/tv/8mD1bwDRbQCOXSW/YZ1gKlEhirMfHCiD75r+1f2/8S"
    "wReADA2IBL+4835e8/ZLeN0ln+KxFzZjZRJj7b/0/L+2/1GbOBgf3xqLsJahYoFXXXARL/YUoVTggjOW8ofvfY3Qmj0+k5D/GtWX"
    "sJ12TJD0z3INR6Z0JBYT4v+mWjLGIKSEeDzGjsPBSamAMAhIuC4L5y/AcZIkqms58ojDMcYgrQEr/sFJtPEN7m/nAO//z3CvrLXx"
    "bYron4j+gsDaPYL6D0+0tVhjovMLgYz/Wmsxxvzfc2ekHF34I+PwkhrfYhFGo01AiMR1EqMrpKNkOOrMCznvrFP5+ecvGRlyTOCD"
    "UQjXJZDRinLMwS0ta4jiBGlRsUiM1Vj7izmiu7SESByrkUZhhcVKjTy4mP2fLOzxQwkirYOmRI5SuR/fL+J5VWSTdXikABcbWpDx"
    "Hj9hNBJyjMM5PurCqmiuMJjQIF0XgJwf0NPbh18JaWyopbE6C4CvNUpK1P8iCxBFnhZlo/EyIlIAlSDgkUefZGf7LtykxzGLjuDI"
    "ww7F6BClnP1LiI9AWIHnJFEIBkplVq7ZRGvHTnb09hMIy9adnfzkj3fT2NjAUYcfyrQJdbgjKy3UKDViy+VLmCKLlIKN2zv40jd/"
    "BsqNtGBYiVaDlEipYmsCxsoRq4WSCgs4ssQVX7iYQyZPwZr/RkCrrSBkilAY2gafZGPHclp7tmM0KOliDLjKMqN5OnNaljGtZhFC"
    "S9AGpIimVAheFjwWIcaESDfFqs2t3HDjPTzx9NOElQqemyQgZMaUFt73tn/jrJMX/68E3QQgLFijsVJgTMgtt/2JQj6gcUIT0lU8"
    "/NiTBJUKxyyYj7FmvMYfMYlSghCKrd0D/Pb2u/nTPQ+xtbOXkl9EW4uXrSOoaKzvk3BgUkMNCw+fw4Xnn87rXnMcVUpg/BDrWpRw"
    "Djhx2hiUlNz/xGredPGX0b6DkJKaOokjoFKR5CuxxrQ+6ZQi6SqsFgwOFtHGJeHBzb/5f5x6zJEYo6OF8l+qfyzWGgQOedPOQxtv"
    "5YWdj2MDn6NnnM6cGceRStVTKg6wdsfjrG5dTsJ1WTTjBE469EJSsjGOBGQk9yNmY68xjDS9IDRFHJni/qfXcclnrmJ32yBve9My"
    "Lr34jVRXpdnWtosrf/gbnlrxFO958+u5/JMXUVtTBUL8L1kDFkw0XiM6dtXa1Wxv72ZKyxRaW3fguB5HH72AB++7l39/+1uQQu3R"
    "+BYIQ43rKEJjuO7mP3HNb29n885+SGdJJtK4qQyeFAhtcdMpSEuMqdAxVKJ1+VPc/fAKjl84j89+8N2cuWQBZb+MdNWBg6t4zYV+"
    "gGt8lh41i0sveQ8zZk2iKuVy211P8LWrrydTVUMh38fnP/pWzj/9Nfh+wKatO/n2D37NC5t6KOZLY3yg/0qtbzE2QArBQLmLv675"
    "EZsH7ifBZM44+mIWTz4ZSIGRUG2YdeRRTKiZywMbruGp1t8zONTH6xe/n7RqwBgXrIpcJbF/PWetQQqPjv48/+8r19LdWeGk447i"
    "O1+7jLQTAj7Tmuax+BdX8p5Lv8R3f/snTj7pOM47/dWEWuMo9b9A7i3WaqwQ7NjZRcKVaOuQSGZwXEnrju3Mm3M4dfUN+GGAtRYh"
    "xvghJgxxHcnugSHe+tlv85Fv/Iyd/WWq62up8sARYHxNaTBHsbefYm8Xfq4XYQwqkSRVU4uTnshDz+3gjZd+gWt+dysJL4k1Bw7e"
    "Rt4eGi5QVZXhu9/6FGedsoDDptQypamWpsYUQVhCW0uoQ5rrqpjaXM/sybWcdfJivnfVZ8kkiuQH+8fjJva/ag4ijR/oMves/Rmb"
    "B59BOHUsmnYaiyefTqAT+MYQYvCtwWjB0mknsGDKa0HW8WLv4zy0+kZCk0cIMwZ/EPu3LQakcHhg+Spadw6hEnDUMdNJO5Zi2acS"
    "pPArPlkl+PzF72FCthYdmpFls0/UtO/rf9T2sW9cEmd99v/pvw+sGIn1DAFSCr561fe59pc3suDww9myZSsvrF/PhW9+IzU11fz4"
    "x9cyd+5cHOVijUFaq7GmghKWjsECF37yq9x67xOk6xpxXEFofEIhyA8XqRWGZUvn84mL3sjH3n42i+dORQcVyoUKMjRYUyFZU0Pg"
    "1vLpK3/M1399E1JJTKixYQhYNIw+vI6Rhva27Vx43mnMmdZCEBQJTYixFhNYLC5WarACHRqMtQRaEAQBRxwylTe/4VR6+iLB11gw"
    "JvL1jI4HxY6AiHtNwP7QITN6d9Eefdtg4yMHmBgL2AC0RAiXlW1/Y1PvU5AqU0szr5p5FuChpMKVDkpKXOEgZIjA49jpr6NGVCOq"
    "KjzTtZxVOx+KkIjosfdzRYtkD0qz/sUtaC0QFipBERAo6eAogeu5GONz1MJDWLzwUArFXHwKzZ60ox+5uVgMOnpqa+P3NBqDGTMq"
    "xMe1tfEYBdH5DNH4YwkBHSs3ayC0hsD6WGPiA2NWr9Xxp/fM1sgMGWv3XNVGbqSNPx0CgbZIHLb09fLgii24Xi1JR/Lmc85CIrjv"
    "geVsbd3KkgWHc9KrlkT+vVI4UVSgKFvBJ/7jOyxfuY7q+okEYYgVCiEsulLkfeefwmXv/DfmzJ5KMh7wAWN58unn+eZPb+DR5zeT"
    "zFYR6ApWKhK1zXz1e79g9qRJXHjmSZggQNjxZlvJ6D/l0hBnnXka1lqUcjBWjkJxY7XdCERnpUQIibWW1512AuvXrY9MmNUINfId"
    "J7IoxiKkiKKfEcG2Yo+5Gec9CKSIhMoYOxYIR8b3YtmPbywCMCCkoK/Sweqt9yHcAO1bpk44hLpUC1oTBfzjvqewRtKUncLkhkMY"
    "6OtCpEKe2/YI8ye/mqyajDA2To2IvcK5PTpvYKAPS0gimeKJx9bRO1ymsUqhTRkhPazRSAmvefUCSoURt1BhjYkEE4mS0XNZK6K8"
    "jZJjoFgfIRUWJ1IHxkboEAIIMSZACBWPsUJgUeh4yA3WhigngSAJwmJMCFoipYwtmhx9LGHBGA3WIpyReQ4jjEuoSJkZHyWj/JJ0"
    "HMDjhz+5hd3dBVzPRWtDU1MN77zgDfQOD5JKpMkmPLTWowkUaUONkA7X3XEff7j3MdL1zYRhBSMkKBc/n+MT772Q6778URbMnoow"
    "efKlIYIgpFYEnHXcIm790RWcvORISvkhXBlrA5kgcGv5xk9+w86hAkI5+5hUx3GwwEX//k6OXnAYCBMHpy+PgUoZOb9LFi3ggvPO"
    "QQiB4yTQeHTnNEMlHS0UJdFC44cBGI2xIEU06PvsQmCsARMipYNUDkI6SKEg1jT7N7kaayPH8cXOp+nztyLdAEenmD7hSCTpA0Qd"
    "MkKmSDFjwiJkkEJ6hp7KVrbsfiaCNq05sPmPT6qUwBLiJZJs3t7PN6+5HitchBL4gUEbg7GGc5a9hkUL5mAxCBkgpEYqhVIuAZAv"
    "FRDCIpWkoi0DxQpGOCiZQpsIDg2tREmXEMVQoYLGQ8oMBkkQlketq7SR1RVSIJ00Fkl/rshgpYKQLtJRGBmgRQkrNMYE6LCCFSFS"
    "KaTjECIZyhcQwkEIxUChQllLpPQIdYgjE5QrmiuuvZFb73iCZKYOHBelJEp5BLrEhOoM2YSL1jrC9WPN60jp0Fuq8Ovb/opMZcFo"
    "rLCgFJV8nlOPmsMXLnoToHn0+a1c8b3v8bXPfpTFhx1K4GuszVObzvLt//chXvueTzBQDvCkJdSKRKqatds6+NO9D3Ppm87G6HBU"
    "k4zdmhsb2GP/BAJ9EMIfeanKg4bGerZ19vO7m+/imWefo1zJE1QEU6dM5ISTFvPGc5dRm/DQoY/yFL+46Q5Wrl5PTU0NOgyRUpHL"
    "5zj71FdzzrITCLThxz+7nh1dBYqVAkfMaOIjH3jnS+QWHIRwCGyRtt61BK7FtYqUU8fEmkMiayA0oMZ9OyJ6RGdsqppJUqWo2CJa"
    "+GzreoH5k89ByZExkftKvY0s2MSWpsi1MxYvW8Ov/nAXPgFf+fQHqMk4VAKNxHDknNkIwOCD8ugZrvD8hk2sfH4dyx94hNefezIX"
    "nHcO13znJzy2cg2+FcycPplzTz+efzvnFBwMubLhJ7+4kfuWP0muWGHKpGZOP3EJ73jLWaQdBxM/pbYgVYJtuwb43U0PseqZZyiX"
    "CwShpGVqC6ecspDzzz2JuoQCG2KwaAHFYsC6zVtZtXo99z/8GHMPmc5F73grV3/vF6zdtIOqqizve8c5vOHsk7jyh7/kzntWsLm1"
    "FzczAS9b5r5Hn6W7u49swvDxD7+b+uoE1mqUcvaaMal4dv1G1m1uxUtmwYSxeTfYoMwbz15GlaPo7B/g0v/4Ps8/v5EZs+7j6C/O"
    "wfUSQIKiX2LR1BZOO34JN975AF5VNcpopAnBTXH73x7kkgvOwpViNDWzd7InWohiNCHGQaTzjTEIoWjd3cd7L/sSTz69kfPOOYWr"
    "vvYxNrX28+lPf5Pb73mO++5bybXf/BR1VSmMNUxqbmL5Y7fQ2V3ATXgEfoW66hrefP7Z2NAipEdRww+vu5mjj57LWacci7EWKexo"
    "xnX8AyiQUNQ9DJQ6sMpBa6j1ash6jdHjyBGR2Cs4EJFgVyXr8VSKsgbpQE++g3w4SJVTixqXvR5HOAHgpNccx89+dRehsSA0yeo6"
    "fnPLg2zZ1M6Vl3+II+ZOJdA+6ApIiXI8trV18Y6LP0fr7jKVUFMpBhxyRJH3X/ZVhvvy1NY38/Tq9bzY2sc99z1Je3sPl11yIR/5"
    "2KfZvrOXSVNmsrljC5vbN/Pgo8+xfuNmrrni4yjAWo0QLq27B3jfZV/msafWceEbXs1Vn/gcW9p6+MTnvs0d9z7KPQ+s4AdXfpbG"
    "qgRKCrr7h3n3xZ9k3bYBSjpJoTQATj2f/tK3eW7NC5SpRetB1nz+m9TU1bNh0w56+nJUZRspGYtUhrb2Tvp27aKpxqXy/neMWlWx"
    "j60Fnl67kXIpSgppoTBC4JgA6bpMmjIFa+GFF7eybedOUlNm8Js/Pci7P3sVdzy2kkefW4s0UXB0yNTpCG3QwkELCUbjugk2tHay"
    "o6cXhMJYOw6XjlxoGQvFyO4eFMJgrUUJxc233s2qDR00Tmzmkneez7xpUznvxIW86x3n4KXS3Pvoar597e8j86ornH3KUn7z868x"
    "sbGBVFUDyaoM06bPZPHiBdjQ4EhFy9RJLDpiNnf85mrOO+Ok0bB8vwswXqj5cj+5cAAlNcb6eELgyiw4xP6p2NdTEZFzkHYypN06"
    "rJYY1zCkeyiVd+HgYI3aLxIiJPgm5PhFczn/tUsYGu7BUw6EkqrqCaxYs4O3vP9yfnnr33CUh5R70uRNjTWcetpxWOmRraqmoXkq"
    "f7jtbyyYP5uH/vwD/vLr/+Dyy95OwkuQrJrC9bc8wHs/eQVVVWkevvMX3Pazy/nOF99P1rXUNU7nljse4W/3P44SkjCsIIXkz3c+"
    "zKrnu5g8aTofeu87OWx6C687YSEXvukM3FSGux96lm/9+EaklFgdUJNNcs65y/C8NKl0luYJLTzz9CaOO2Yhj/ztV8yY0kgmmcE3"
    "GZY/9CTXXf0l/vCrb5LyDNIqKsMBbzvvJFbc/VNuvf4aGmsykZDvhz8mAfr6B8bImcAiEVisDijk8wgszY31pBwo+0WoruLmR57j"
    "/Pd/iS9++6dYlUIIwUAuHwfEYhRalEpRKpXo7++PsedXEGuMr9Oxswdpkvh+BUE4mohbMH8ungiprmng9juXs62jG8dJ4vs+S+bN"
    "4C1vOIV83yCJRDVrN23kplvvRyYdBocr/OzHt/ChD7yZ5roMuXI5FlwFVo5ZuCO7jYP0EkHgjwblSo34lPZlYTmlFK7rRkF6TAw0"
    "48hVe+8SERM8jNF88dOXcMJRM+gf6CH0UoRWk6lKMFgM+NwXf8znrvgJQxqEklijyaZTfPRD72Nqcz2Vso9fKdFUn+KSi99KSIi2"
    "IW88/0yaGrNYfAqlEo898hQfvuRiPCXxg4DXn30CC+ZNp1TMg0ryx788GMdfkWXb1rYTQwVpirhKYG2AMYZDprSAhqrqBu5/8Ak6"
    "uoeQ0sFTmo++5y0cPX8WfmEIowPSGTj/vNOZ2dzErKkNDOeHCXWAIMR1HWqqk6NKUAhwPZd0KkVVVRXqJfIUEkCHenxy0MpRn/KB"
    "x5/CCMHc2TP5xMXvJFHqpzK4m6CUY3JLA5/56CWkHId8pczjT69EekmsjqbFijG8k38SP8QCZy87idqUYMnCORx+2CzCMAAESS+B"
    "FBYrXIaL0LqjMxJIIbAm4EP/fh7zZjfhFys4iQTf+ckN9BZK/OqmO6mpquFtrz8dbXwyCQ8Zj4fBRAmTcfuYioT/9LqOUSy7b15g"
    "3+vpGNoTOFIhMEysS3Pddy/n1OOPJD+4CyXDKOh2k6RrpvLz6+/i0i9cSc6PIUFdxJOadNLBIvDLRY6cN5uJ1RmM9pFCU51NMGVi"
    "A4H28bVh7tz5TG2ZGCfOLAkBM6c0Efg+jpdhc2s3w8UKSnkYaznz9NdQn9Usmj+Z6ZObCYJK5NZl0mAFUqXY1T3E5i07QEqwGmsM"
    "2ZSDwBCGhkmTamhqyGCN5qJ3nMuUCR6zptZxwXnLsNZgTBgF6yICPUfGJmIgHDhOdEZ85bEDLiwYbXHTNdz+wAouOOd0zj5mPpe9"
    "6wKOPfwQHnv2eZIJjzNPOp6FM6cB8N0b/sxzL+4gWVWL1eJgXPR/WOSVlFhtee2pi7jvzh8yqamRKnfs03kRyU4IjPbJFwrxuhZo"
    "DRMbq7jswxdw2Wd+RCpVQ/dAP5+6/DqeX/s0X/3ipXhKRQM4airtuNejlxGRZnEcheMo/Hih61DHy0EcVLxitAEhRgzvaNwj5d6I"
    "2PhzucohND7NTVX89vtf5OtX/4Jf3noPoUqR9BIExqemoZk//+UZDp3xey6/9N3Y0EeIGDkXIIymIZuNfHTjAoaM51CVSmGNIhQG"
    "z1OkEgohglH6eTrjgjA4yqGQKzE4OEx1egI6CFj2mqN4+M5fMGFCI1lvjxAKz0MJjRHgG0u+VIxGVEiElBhr0EJitEM2naQqnUYY"
    "y7JXH8Vfb7oGmUgyrb4aMDjK24P6iyhWFKNQOC8n+HsIUWrkolaA4zLkWz74hW/w48sv4+zjl3DqsYs49dhFoycohCE/vfE2rvzp"
    "jbjZLNaEcQBoEBi0UFhh9sJiXkHx1xVQkumTG1m1ZhMb1mxl/ZYtdHa20dldRrnpOCFisLHWtoCQijAMOP+1x3P7Hfdzz+MbqK2v"
    "4/Y7HuK8c5dwxomLMUEQ4cQxyzSwefryO/CNP86FCbBMTB1KTaaehOdR0SFCCIywWFOJABjpI0jsherYOBkFFV2iWBnEEVFiyFMp"
    "sk4Nw2EX/YV2VIxhYwUWg5KKidlDEKQhjnUqWpNx4etf/CBLlx7DV779c7btHCJdVYNvDdmqZm64+W7efN4ZzJ3WhPX90TkxYmyi"
    "bw9PQoj4OAJhLdLaOA4byZs6WCOxRJBpaEfiD40jXWZMbmLF2o2sW7eVjRu20b6ri67uIRJJB0OIEHLUpWN0fqJMgNwrbx1qzYxJ"
    "9YBDqP1I6K0Ylar95lheSvCtAOWoKKNlLS4hFnApkU4oenIV3vaZb3H2KUs5delRNDfUooOQ1vYu7njoSR5bvQE3VRUFKWMeItJc"
    "EmEEdhxi80pwRATGGBwvwePPbeKK717Hc6u3USqVeM2rj+D4Y45kekmz5Zb7sCIRLcA4aJZYUBYRKpJK8OmPvZ1VG66hFFi8rENQ"
    "DtEVixIaYZ14WAWlIM+fH7+O3mATjnAjopiASuBwweJPMmfKPDLuBIb8PoRjKOkSfjgMzoSoPnl/KffYIBSDYUpmCMc1+FpTm5lI"
    "bWoKazqWc8cz3yfhRsklISyhNjQm5/HO0z5JSmUxwiKMIakSWBsJyLmnLeGYI2bz+a//mr8uX4mbzuC6ip5+nxVPr2HutDMxxiII"
    "UdZSlhYtRzzdiPsiYtkQGGQMxUZAkozhZ8AoLDLC4qWIibQhjpNg+aoNXHP1T3lqQxuVfIETly5m6ZL57O7Psan1IZQ1KKMQ8ciM"
    "sQlICwKNMCJKQEqDQkb5EixSuqO2zyIwQmKFRFp58IKfK+TQA7vJCR+0YrQG3ZpoV5KStdx081+46ZY7wYmKy/Er0et0Bj08BCbG"
    "38cGYzZEk3vFCyFMzOxcs6mNiy+7kl39IQk3wdcvfy8ffsfrAHj0+Rf55e//hCOysS7YAwsKK0EGWCupqW1EaShVAtKZRu59eBW3"
    "3rWcd73hNLQJoyyhdfBUDScf/VYqNh8jUbHUGk1L9TQUKSbXHMbOoS0kPU2+PExPsYv6utkIk4rpxuO8+gixUdBf2EUlDJFJifVd"
    "JtcdBjhMqz2cNxz38ZinL2IiHDg2RVJN4M67H0G5irNOf3XEQZESJSVBENLS3MC13/o47770Kzz0xGa8qkas9ejq6N/D97evHD8n"
    "mpgK4LBqfSsXffQKcoMBrlvFV77yAT7wtjMRwN8eXc0NN9+HmxF/tzs84v79oyCJA3DKq45GKEV1NkNgFMIYhDW4roeQAq1DpA0R"
    "NkolB3GyWgFaSAQGYX0wgjAkxrzjqhfpYIVPY13tOCTmH/Pu7ajX/LMbfk973yCJTCOHzcpw0dtfh9VRAXw5V0HYNNY6+0yusBCi"
    "cYTL1Vf/hOktWZqQbNi6GyfdwPd/ehOnnLCYyQ1ZtPZRQuGqJHOaXvWSdzZv0jGs6bgbYzUV8uzoX8ecuuOwRu6TkxOjZSQBO/vX"
    "E1DGsZIqJjKvZSkAtemJ1GZa9qV0EyBQbN6+i83bt3P26cePuipCCFzXIfR90p7Hh9//Jh5/8kq0NSAsqXRyLIi3T+TwDxGWbUQL"
    "+Pn1t9M9ZMkkssyf28C73rqMUA8gqaGcDw4K7BjhC9mDJNwaYw5awTpWB/z7uct437nL9jlYspZiJSAw4Lke9e6+JygAuZJGiCjY"
    "bPDkPvfojzg3xkbR+ysA5UglKZR9Vq9pw8tkKVUGOHz2HBICAqtxHQ9rw2gRi70iCyExOsRxXJ55YRsPP/wUN93yQ9p2dPDej1xF"
    "onYGW9va+eHP/8BVn7+IwFqUsGAlIRpp9tLcoUB7ZYR1mVm3mNkTFrNu92OIpGZb1wtUZg6SlLX7YVoahJDkwyHae19AJH38imBB"
    "07FMzB6GwY8skx6txdkzBCZKd6Sqanl0xfMM5AvUZtLYMXwopVysNUycWE9VOsuwLiG9CjNnTR7jbI2HZA+u7OPAFGFHJQgCzabN"
    "7STcJGElx7xDjyKFQIcJVEJSDv09GvsVZtKK0QUzAnHu/34dIRRWGwIT4AiDcFLc9cwL3HrX/ax6YSO5YogQLjIs843PfpALTllC"
    "qTBMIpVhZ3+Oiz79VVo7dyO8FC6WWVMnc+bJx/O2c06hPu1SLhUwjkQ4Lko4o7DgwWzaCrSQaAFGGvbEyNGLwUKRQqGMIzyUDsi6"
    "Gay1hEGAqzx2dPRS1mUyqhxNl4lgrlAHSCxWpLnqO9dx9tmnsHDWVObNmMwZpxzDXQ+vJ1NTzy23P8Cbzj6ZxQtnYYIyUqUxUoLa"
    "y3rIOEliBcJ6nDD7rXT0bmXItNNTbGVLzyqOaD4NE1ikjMlyQmE1CFezYddKOvN9OAnJBDmDpYeegTtCiBMC64j9oDoacEl5SbZu"
    "2831t93DR9/1b1TKORKeh5Ze7BIJdDHE6jyhcWmuq2PRvNlAEEHOVmCEQNoE2sYxmpUYozEyRBkHaRxwwApBKHxc66IR0TBIgxVR"
    "8BuBg5qKHxJUQApFSIibdDFAqBXKWjr6u/ExpHAiPqjVGGMimkMM4QoZeQdWWDQjDE3B3mlAIQRKSISRCKsIdCTsjvBBJCOOlRix"
    "Y2OKza2UCAmum6C7CJd8+Wre/IHP8evb7mXdjm7aenO09w6ypXuIT37tB6zevB0vmaYYWr7wrWu5/+l1dAyV2N49yIaeYf7y1Bou"
    "veL7vPZ9H+eh1RtIprLIKM2CFX9fGxIlJdJalLVRxj+GDRE+YKipSlFTk8GGIa6j2Ni2BSsEqVRUwPHg/StwbAplJcJaEk4iCsAD"
    "H9dNc/fylWzfvp1PffhdWFPBk4YPX/Qm6lIGZUMKJcM3vv8rSlpElxY+EYVu/D8ESBJIqdDWZ1LVoZw+799JlxvQchcrttxOf9CO"
    "cQ2+CAmFoCI0xnXoKnfw5LZbCFQ3qUoTZxzxDpozs+LyOCdOVO19zT2j6FdyOMkUP/n1X1j1QiuJZBUmFBBqjC0gpGDVuq0U/RJ+"
    "ocTZp76a6S0NWFMEx0FH6VyUAWHjQnijUdZGhDUdsy2sQVmJowTYAGX90YIOaTUOBmUFQiqSSUUyFWKkj3BTbN+2CwQk02WEEKxc"
    "sQ5PJHGMQlIhlRYRgUwbpBBEZFoTnxscIRCESBuMcceiLZtJkUhE1PpEOsMDj69iS2cvvXnDzvbdsfnT+5gWGZoI++zqH+DCj32B"
    "n962nDBTT6q2ETeZxvUcXAcyVVna+op8/IofEFr4+Y1/5Ma7HyfVNBXhJkm6ioTn4WWrSTZM4JlNHVzwkcu5Y/kKkm4qoteO8tpf"
    "PoAxwNoXd0QsSeEhSLNhU0f8fQ8TGLJegrNOX0puqItEJs2q9bv44e/uonsg4Fs/+Q09Q720TGrE9y0imeWeR1by8JOrcBJZdnT2"
    "89Urr+XEk05iUnN9lPQyAYfPnUPzpCYqlYB0tpGHntnOtdf/FSvTsTY0L2H+LUJItDEcOXkZZx91MbViFjv7NnHHM99nMLceT0aU"
    "iITQ7Cqs5bZnf0T3UCsT3Cmcc/QHmdN8Qlx95e0pJt1v5tEDLIfNa2HSxCxt7T28/zNf5tHVG5Ceh3IcEm6WZ7fs4urrbqUvX2bx"
    "vIl87OI3EZoAIbO82NpFd+8Q0kuj0g6btrXRm6sgHRfhJGnvLbKlYxcy5aHcJDt3DdLaPgzSQ0pL3g/ZvK0fz0vhOC6FYsjmLT04"
    "yuGE1xxJfriHTKqeVavb+PnN99HdD9+97kYGBweY0JDGD0tIL8M9y5/nsSdXI6RHe/8wW9p6kV4S5SZp3zXE9p29CLyIRzYmjjHG"
    "UFuV4rhjjySf6yeVrmZLe5ELL/kap77hQ/z0+j9GkZQx+8Do6kuXf+nLRSP44OXf4q5HniPRNJVQh0R2K84cxv6tDkMWHDqFt559"
    "Khtbd3LX488jvBSYIPIWrUQaEKElnchQKoc8vGIFp518PJPq66PgQ7y0szNSh/vjX9/MVd/7FW4yiR/mcIRg1VNPUV+XYfGiI7Ah"
    "WGGZf8Qs+vr6Wbd2K6WC5IEHnua3f/gr7Z3d/PAHX0FTZPkjT2Cs5IknHiWZUUjX4+3v/Sit3YMMDvZy2onHUd/QiBQuv/z9n7j5"
    "T39FuS5hUMERkofuu5dMKslxixeh9YEygrGJFgopHKyp0Fx1KC0TjsZoza6+Naxue5L2oQ20Da5h5Y77eHz9H9G6nyOnnMnpR17C"
    "zNqjsFpFNOgxOa99++9YhIz82BmTW1j6mmMJfMn6Tb389oY/88zzW3hu3TZuu+Mhrrzq5wwNFfi3153IVV/5IDNbGhFIdnR08573"
    "fYLdXYMYqRGyRHtbO2tWr+Wcc09nKF/inR/4FGs3t0ZZUVuhf7CfJx57jNPPOJ5stoaPfOY/uOu+FTgJlyAcJggqPL78EU4+/hiW"
    "nXIC7Z39bNqwnsHSEH+75zl+e9NDtLe38qMffInA5nn48SfReDz22CpSCZclSxfxtos+xgsb25HKoG3A0GA/Tz75OGeccTJV6ew4"
    "FsBInDB9+nQef+wZdu7sxBro2tXB1JY6Pv/JD9BUXxXHUuNrv4W11v7ub4/yrs9eTaKmAWFKaBEFcALQUmIEOEh0ro9fff0TvO2s"
    "ZewcGGbZ2z7M9v4KrqsIiXxFgY7JnQLluhSG85x/4iJuufpLODJKjjkv4fCMpJo3bNlG5+5hnEQSISooHEqlkJZJWebOmoLEi1Ly"
    "aEKb4NGnX+DZ518gl88xob6BN557JhMbBaWK4r4HV/Ls2heYMW0Kb7ngDPp6etm8ZQcyXY0Jyhxz2Axqa2qxxrJx+w529g6QSCQR"
    "YWR+dODT2FDN3EOmIoVFSW9fmY/x64jPI6JKJiNwlESTo6+0k9b+TQwP9BAGPspL0lA7gekNs6hPTkNQHS0qISK0R1gQkv3zQTWG"
    "MlJn0LaCciQWlx2d/Tz73AbWv7iJoeE8QsGMaZN49eKjWDB/NhBitUUpl8F8gVXPb0RJD6nAKh8bJHCwLDl6OkEAT6/dDq6DMiPY"
    "k8QNDQsXTiaVzPL8mq0UKiaadxkiUZSCgKPnTGVCfS0l67DiqWd4Zs2L5AtlJjU1cMHZp9FUV0Ul0Nx5/xOsXr+RWTOn8JZzTsOa"
    "CqvWbkKQQYqQEBkBGSZg4RGHkk0opJMYF7BqEyCkYWvHAHff+yi7e/qZNrmF884+lYl1KSz7Jg5HBf8jV13Lj264i0xdHUYHWCHG"
    "JQeEgMDXTGvM8MQN36apthqE4mNX/pDv//4BqmoyhNrG0KYeo6kEoYHmpGXFLT9iakMtoQFH/mOQprU+Is41WGOxQuxXCxtdRkpv"
    "r+5u+2v2E1VbaQxKyAMiF8YapDgQljC+FYgdSaNbE4mueIleP3GRixhtr2bHcfbFfpiZFoOwKspJx2WEUnoHrGOwNsBYixrtQiFf"
    "AqEJYhxOHpCPGsFH6oDHrdVxJwdn33vXUfHT+MuP8LrkS8y7jsmCe5UBmWBfZQRR2xUp93tOJ6qAkyP5r9G0/tjhl0IQlvKcdsJp"
    "NNfVEQSRlj/rtJP46W2PxBlAsYf5bPdE3NgQ5XgxkevvK9zeN0kx0iXMjfp1Whvly+Is7p7PR5VcUiXBRt0jRmIHpeQ+55YyDlBt"
    "NFhRdjAOIcXYskd5EGDaWCxcxsIR0wGsxY77zAg7QO6PsLyXm2P3ekeN9i2SwokTW1EntX1yFkIgpYvaS9AOhHmPZEUPfFzGdTBR"
    "RdselEnG14rmaOQaNqbECKJWMUI50YjEpY8AUqnReTzQNcV+F5pASW+fbnFRVZ3z0gmsl8NSjYV0QvH6k5dEC11GN77kyMM4YlYz"
    "q7d0kkilEVazP9zmP5Nl2x/RyI7Rf1IYrAjiBZuMqBF2DzYOMqodFQLHUYQESOvEOXiDEGMFyYyYv0hDqSC+b2dMt4MRpuQY4RMv"
    "hWuLsfD2AVNDYrS0Whzwe2Ovs/dY7qGAA0KjlMXgjlZojbQsHLn3sdj2gTBuO4LoyANXIIzUDEcFdRqMGwX+4+qkRUS6lBFUOcL4"
    "HTm/kGKfc77sNQ9gEYQQL0lD3i8t+eUEsFLxOXRaC8fNnx3fsMJoTX3S49TFR6KDICKixVm7f9pmokEdGO7huRcfY9Wm+1m16VG2"
    "dKyLklXCIIQexY6EtIR6mE0dKxkotUdumLGjVk2MLqO4jl9G5n+4tIu12x+mbHJ7LQ4NIp40sfeE7C/YjXoNiHihCeK/wsSx0IjA"
    "qxgtGtHWGksYf3ZsB4j4u2KEhqtHd4GgZ6CdTW3PRsWbRoMI4u+HsUIYaRZm4vGyY/aoPFLE3Jx9O1Hsu6h967Nhxwp6h7aAJI5L"
    "Ru4pQmAqQZ51rauomEKk9QVjnmnsGJpxFXmjx+1YBfXKZbteVvClFJhKhROXLqaxKovW4TjZft2yE/CSicj1+Gf3ZIxPXyoXqGtI"
    "0pfbTjorsQQYUcHXwxjKCFxCE1IJ8winyIbtT9E73EZoi6AMxoYYNH5QxhCODoMflkBCxVbYtGN1NFkIAl2IP+OCDfD1AL3DHeQr"
    "PQRmiEqQxw/L44SkEubiIDREU6YSFjDCJzB5QluOSF3CJ6RAYAbiOETi60EMRSxlKrqPihmgYoao6ByVoB9DmdCW8E0JhEVTwTc5"
    "grCAlRVQfvR8MqCih9C2GPncBAS6wFCxi8FcNwhNJczhmxy+zuGHg2gCKmYQI8qAgyX68Y+o8YiPoYKmhK8LWOvjSENH3zp29q1D"
    "Gx9kgKaEwccQACUQIcIpIVQFbYv4wTDgYzBoWybQJUY6LfimQmgrCGEJbAU/LICIPheN5ysn+M6BjMpIu1KtLUnXct6y4/b4VBis"
    "BGM1i488jFfNncKjL7SRzGQRJhx3exHLbs8tm3+EBiICNILJDTNBTWBz1/M0VE2muepwNnc/Re9QJwnpMGnSoXTu2kboW5ob6qlt"
    "UfQNtdM12M305qmoQLK+/Xlm182lvdjG8YedRmdvB1t2raMu28RhsxdSlUqiRMD27mfZ3vkM6dQkZkw/kh1bnyYUBQrUkHEMfnGI"
    "SRPnExYMR8x+Fb6psGHnaopBJ3WJeqzKsrP3OSbVzqc3187Upom0tvcwb84RbN6+EiME1QrqGuZTlZzIlrbHKfgFjpl/EqvWPYCX"
    "9RguFZhWv4Ag30fzxBY6dvcSiEEm1x/G1q51pJKSejGJYQZJekm6chtZufUR5jTNoqd/JwsOO4cd7S/gB7305nuZP+s0asREtrSv"
    "pK13I3NmHEmhr5+Glvls272S4lAPiw4/g3UvPsjs6ccwNFhA2X7SVRNZ0/koUzNH05SqZ8rkBVRXp+kpdLBm8+Nk6ix9uQHqvUaS"
    "iTo6e59lZvOx9Ay30VRspm33CqyFSVUzebFrPbVZRZAPaJg4j2wyy7ZdW3Gw1NfX0p8fxDGW+mwTfaUuQl1iZvZomppmvSQV4RXR"
    "+FJKKqUyxx+3hBMXzifUFZSMG/4IhTWajBC88w1nIXQYa61/ZhszJ3YLokWntSEwEjBsaVtFuiZBf66D5zfdhXQM8w89jrr0LPyC"
    "w4S6JtKZDJ2dO0mlEgznB5k6tYWhYg87ejazK7eDRYcfy86dW+ke2IFIwe7cbnbs3sSCw0+mZ3Arz236IznRhZPJkLIZFs18FQEh"
    "JHwmNk8GXIbK/Wzc9RQ19Slad6wHNUglyDF1ylS6+tuorppKKHP0F9vRlMlmJjBxwnFsaL+XTV1PMu/QE1Ha0N62k2ktx1Dyy2iZ"
    "J7D9TJu6kI7uHRTDbgRldvduIjSDJN165sxYglIufb29VGUyDA0P0dIyk1Lo09m/md1DW6mbWIcpu0yqmYYwgulTpqFthVLg0zJ5"
    "FtvbnuaQaQtJuUm273oEo0rky0VU2iVXKuC4LuWiz6EzFlBfOz22bIrampk0T2pha/tGQlEhV+7BTSv688O46RT9w0NUQs3m1s2U"
    "TI7q2gx53UsiXUt1XQs7e9ewpf0JRLqDXKWLrR1r2b7rGQq2D5mCF9s2MBwM42bkK1bNJ18aWYkyXqVymYFcHqUE2oQIK9CGqOhA"
    "CHp7exGOjP3Uf6K7Y2OITUTsTyUTMUyoMbZC6IfMmXEk2dREynlJ1qmnOpvFkylSTgOeSuE5SVwvTTpVh6tSeIk0Vgq6errIeI1M"
    "njQzxoY9UJKegQ6y3mQmNc4hnWjBqCxlozlkykwybguWJJ2dbdRlmuIowBDaEq6oZ/6cpaTcWjJuM55sIOFl8Zx63ISL4wgcJ4OX"
    "MLiJMkhLT24HJb+f2dOnEQQFpjXNoZgbQtoK29ueJZ3MYm2Zih5k2oSlHDL5VXhUkZS1OCpLJhE/k0qTTtTiiTocJ4OTFGTqUnT0"
    "djN75jxcEhjfknGqqa9upLOrlZpMPUO57RRzfRx+yHyUrcIRDVGOQOUxqoTratKeR9ZJkUomI76PAM9L43oaqCBJxbUdEksa6boo"
    "JyCZEsw+ZBqdXVuiMc1mcd0GlFOL9IJInious6cczczJRzN72lG0726lb7iD+fNm093XRlvP5v80WLJfwRcyioiVlFEzH6WiCFlI"
    "MlVVPPXcOt712SvZXQKlUlgT8WcSjse3bvgzV1z7e9KZLAqLiL87dpdSvTLLQegIYxZQqRgGBgvkcj2Ay5TGwxnuCQjzgkMmzqWQ"
    "7+DZTX9hW9eTDObbKeSirgUDw9vp7ttModJD/1Ang4OdpF3LhJo0j676E9XVkqyXZqCrjaQwTGqawONP3kSVl2BSw3S6u7bTtrOV"
    "/kob4DCxbhY16UaUyIA2NKQmMDEzl56eXQh88sN5hgsdDOZaKecHyOVepJwfpJgbQFJgZ8dmtrWuZmrDEg6ddByrnn2EwbzPrClH"
    "kRKSybUzmVG/mJaqOXgEzGw+FlNOMjjUSegXKRb6KJbawYYM53YxXGind2ALpXI3A8M7yOU6KOT7KJZ62LLjSboL2ymYIXAsggRT"
    "GuaQdbO4oo5Dp5/Ac+tXsGNnJ4dMWsiE6np6el5gaLCVQiFP/0A/heEC5VIp6jphJVWJRvKDOdp3bGdG80Ka61ro791CT88WKkE/"
    "u3teJChWGOotgp9g5qR52EAzPNxPLredfH47w4NDTJ7QQGlwmKDcS1jqx1Z8Zk2egyi6hAOSWc1zSIjsKxcuWmvtB674AT+77lZE"
    "QwNW6zFwVeydSweGhzh+6eH85qrLmdU0gYoxXPmz3/CV7/4WMg2RUNpwX9KNDmmscnj69l8ws6mRwIL7nzRVI8GWsg5BWKGzsJWs"
    "k6YhPQstC/QO9JJWSaqqJ5D3u8nlS2SrGhks7KZa1VJ2SphKCVelKNoKtbKBwbCHereJZMajq7+DhppmCBLkCm1kUs146QSD/a3U"
    "Vk2kc6CTjsEVSC9J30A/R888g3wpR21tLY2p2QhtsMJQthV6BzuZUNVEObAUwjYybjOFcolMwqEUaFJegtWb7kJls8xrOpps9URc"
    "svQNbcdJJKh1WxCqGLVkJIkwGlcZoJqB8i4qlSEaqqbSX+jCVUkakpPpLnViTJmkyjCsh6l16ykFvSCy7Oheg5fWbGvbxsJDTmR2"
    "43wGhjsZKg2Scqtoqp2BkZLu4kY8U0VDZjKBzTOQ343j1uIIQWhylPxBJiQPw0t4WC0JZYGBfC+OFVTXNGFwKeZasTIDroVAUAx6"
    "aEzPouAPE+gyjdkJdOb7SMqIEVAIYVJdPYO5HOiQutp6+oZyaIo017QwPDxA2RRoqp4eJb5eGcE39vo77uEvj6wila3Bah9NOD7R"
    "YUEoRbGvm2VLF/Oht1/AyrXruea63+GkazEqEbfuHc+Ck1ISWkNDUvHFSy9mYnXVKxKYHARd/xV0uKIOaBZDudRDR992jLIkUxn8"
    "sqZU9pk3fRGOSPx9yKwd5Km1j5KqrWXRtOOwxok5OPJlnuI/83Qh27s2Edgi4DC5cQZJlWRX3w76cruYN20pnkrE3QrkP2UU/7tt"
    "wuqCRSY52J/DstZHh1H62/Oyf5cwHkQpw9+d3d07ubPn/3a0KGP079j53OvYSDnbWAJU9FJjrYqz6RpjQ0JtUcqLeevgKOKmsnvf"
    "29j7sDE+rdDaIESIUGGEwNsEEoUVUaNVKeRLjtJIK/TR33UScRnj6Pvj25xYodGEVHSFhEzjWDcmmVqs40dMTyviMbLjUm17xmEP"
    "rC7286z7kMfE2MKQ+F73c98jwjG2s8r4Zxn/+pUTfBPEYxCVEEbZtzEDPyaBYAUYKUZ7igltkUSt9WAvsv/IL++FUYZOOGocB+h/"
    "xjbSkNqJ6Tx7hGK08ZMl7sZ8sOdSMSUi+vLI7zZFmVcTM2jkK/4UJu4aLYwZL1xC78Nc/L+wjf4U0MsZtvH5wz2RsSTK1uq4tkru"
    "yxTCiIjhGR03B21d/ntsB8Mxkn/HIhpbiB+pZh0XkqvRhjr/TB8w6oIfzYIcab3L/7Xt/wNwNfZj5GgxpAAAAABJRU5ErkJggg=="
)

LOGO_RIGHT_B64 = (
    "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"
)

LOGO_HERO_B64 = (
    "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"
)

_LOGO_CACHE: dict = {}


def load_logo(which: str, height: int = 44):
    """Return a Tk PhotoImage for an embedded logo, scaled to `height`.

    Results are cached per (logo, height). Returns None if Pillow is missing
    or decoding fails, so the interface degrades to text without breaking.
    """
    key = (which, int(height))
    if key in _LOGO_CACHE:
        return _LOGO_CACHE[key]
    data = {
        "left": LOGO_LEFT_B64,
        "right": LOGO_RIGHT_B64,
        "hero": LOGO_HERO_B64,
    }.get(which)
    if not data:
        return None
    try:
        import base64, io
        from PIL import Image, ImageTk
        raw = base64.b64decode(data)
        image = Image.open(io.BytesIO(raw)).convert("RGBA")
        if image.height != height:
            width = max(1, round(image.width * height / image.height))
            image = image.resize((width, height), Image.LANCZOS)
        photo = ImageTk.PhotoImage(image)
        _LOGO_CACHE[key] = photo
        return photo
    except Exception:
        return None


# ---------------------------------------------------------------------------
# Core PDF operations
# ---------------------------------------------------------------------------


def merge_pdfs(inputs: Sequence[str], output: str) -> dict:
    if len(inputs) < 2:
        raise FeatureError("Select at least two PDF files to merge.")
    require_distinct_output(output, inputs)
    pypdf = need("pypdf")
    writer = pypdf.PdfWriter()
    total = 0
    try:
        for filename in inputs:
            check_size(filename)
            reader = pypdf.PdfReader(filename)
            if reader.is_encrypted:
                raise FeatureError(f"Password-protected PDF is not supported: {Path(filename).name}")
            for page in reader.pages:
                writer.add_page(page)
                total += 1
        with open(output, "wb") as handle:
            writer.write(handle)
    finally:
        writer.close()
    return {"output": output, "pages": total}


# ---------------------------------------------------------------------------
# Compiler — appeal paper-book compilation
# ---------------------------------------------------------------------------


def compiler_safe_filename(value: str) -> str:
    clean = re.sub(r'[<>:"/\\|?*]+', "_", str(value or "").strip()).strip(" .")
    return clean[:140] or "Appeal_Paper_Book"


def compiler_page_count(pdf_path: str | Path) -> int:
    check_size(pdf_path)
    pypdf = need("pypdf")
    reader = pypdf.PdfReader(str(pdf_path), strict=False)
    if reader.is_encrypted:
        raise FeatureError(f"Password-protected PDF is not supported: {Path(pdf_path).name}")
    return len(reader.pages)


def compiler_wrap_text(text: str, width: int = 70) -> list[str]:
    words = str(text or "").split()
    lines: list[str] = []
    current: list[str] = []
    length = 0
    for word in words:
        added = len(word) + (1 if current else 0)
        if current and length + added > width:
            lines.append(" ".join(current))
            current, length = [word], len(word)
        else:
            current.append(word)
            length += added
    if current:
        lines.append(" ".join(current))
    return lines or [""]


def compiler_create_divider(path: str | Path, exhibit: str, particulars: str,
                            ground: str, issue: str) -> None:
    need("reportlab")
    from reportlab.lib.colors import HexColor
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.units import mm
    from reportlab.pdfgen import canvas

    dark, middle = HexColor("#17365D"), HexColor("#1F4E78")
    pdf = canvas.Canvas(str(path), pagesize=A4)
    width, height = A4
    pdf.setFillColor(dark)
    pdf.rect(0, height - 42 * mm, width, 42 * mm, fill=1, stroke=0)
    pdf.setFillColorRGB(1, 1, 1)
    pdf.setFont("Helvetica-Bold", 19)
    pdf.drawCentredString(width / 2, height - 24 * mm, "APPEAL PAPER BOOK")
    pdf.setFillColor(dark)
    pdf.setFont("Helvetica-Bold", 27)
    pdf.drawCentredString(width / 2, height - 82 * mm, f"EXHIBIT {exhibit or '-'}")
    pdf.setStrokeColor(middle)
    pdf.setLineWidth(1.2)
    pdf.line(30 * mm, height - 91 * mm, width - 30 * mm, height - 91 * mm)
    pdf.setFont("Helvetica-Bold", 15)
    pdf.setFillColor(middle)
    y = height - 111 * mm
    for line in compiler_wrap_text(particulars or "Supporting Document", 62)[:7]:
        pdf.drawCentredString(width / 2, y, line)
        y -= 8 * mm
    if ground:
        pdf.setFillColorRGB(0.2, 0.2, 0.2)
        pdf.setFont("Helvetica-Bold", 11)
        pdf.drawCentredString(width / 2, 55 * mm, f"Ground: {ground}")
    if issue:
        pdf.setFont("Helvetica", 10)
        for line in compiler_wrap_text(issue, 90)[:2]:
            pdf.drawCentredString(width / 2, 46 * mm, line)
            break
    pdf.save()


def compiler_create_front_index(path: str | Path, title: str, case_info: str,
                                rows: Sequence[dict]) -> None:
    need("reportlab")
    from reportlab.lib.colors import HexColor
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.units import mm
    from reportlab.pdfgen import canvas

    dark, middle = HexColor("#17365D"), HexColor("#1F4E78")
    pdf = canvas.Canvas(str(path), pagesize=A4)
    width, height = A4
    margin = 14 * mm
    column_widths = [12, 16, 102, 25, 25]
    headers = ["Sr.", "Exh.", "Particulars", "Ground", "Pages"]

    def page_header() -> float:
        pdf.setFillColor(dark)
        pdf.rect(0, height - 31 * mm, width, 31 * mm, fill=1, stroke=0)
        pdf.setFillColorRGB(1, 1, 1)
        pdf.setFont("Helvetica-Bold", 16)
        pdf.drawCentredString(width / 2, height - 16 * mm, title[:100])
        pdf.setFont("Helvetica", 9)
        pdf.drawCentredString(width / 2, height - 23 * mm, case_info[:150])
        y_value = height - 40 * mm
        pdf.setFillColor(middle)
        pdf.rect(margin, y_value - 7 * mm, sum(column_widths) * mm, 8 * mm, fill=1, stroke=0)
        pdf.setFillColorRGB(1, 1, 1)
        pdf.setFont("Helvetica-Bold", 8)
        x_value = margin
        for label, col_width in zip(headers, column_widths):
            pdf.drawString(x_value + 1.2 * mm, y_value - 4.2 * mm, label)
            x_value += col_width * mm
        return y_value - 9 * mm

    y = page_header()
    pdf.setFont("Helvetica", 7.5)
    pdf.setFillColorRGB(0, 0, 0)
    for row in rows:
        lines = compiler_wrap_text(row["particulars"], 55)
        row_height = max(7.0, 4.2 * len(lines) + 2.0)
        if y - row_height * mm < 17 * mm:
            pdf.showPage()
            y = page_header()
            pdf.setFont("Helvetica", 7.5)
            pdf.setFillColorRGB(0, 0, 0)
        values = [str(row["sr"]), row["exhibit"], "", row["ground"], row["pages"]]
        x = margin
        pdf.setStrokeColor(HexColor("#BFBFBF"))
        for column, (value, col_width) in enumerate(zip(values, column_widths)):
            pdf.rect(x, y - row_height * mm, col_width * mm, row_height * mm, fill=0, stroke=1)
            if column == 2:
                yy = y - 4 * mm
                for line in lines:
                    pdf.drawString(x + 1.2 * mm, yy, line)
                    yy -= 4.2 * mm
            else:
                pdf.drawString(x + 1.2 * mm, y - 4.2 * mm, str(value))
            x += col_width * mm
        y -= row_height * mm
    pdf.save()


def compiler_stamp_page_numbers(input_pdf: str | Path, output_pdf: str | Path,
                                footer_text: str = "Page {page} of {total}") -> None:
    need("reportlab")
    pypdf = need("pypdf")
    from reportlab.lib.units import mm
    from reportlab.pdfgen import canvas

    reader = pypdf.PdfReader(str(input_pdf), strict=False)
    total = len(reader.pages)
    writer = pypdf.PdfWriter()
    temp_dir = Path(tempfile.mkdtemp(prefix="smartpdf_compiler_stamp_"))
    try:
        # Clone the complete document catalogue so outline bookmarks survive
        # the page-number stamping pass.
        writer.clone_document_from_reader(reader)
        for number, page in enumerate(writer.pages, 1):
            page_width = float(page.mediabox.width)
            page_height = float(page.mediabox.height)
            stamp = temp_dir / f"stamp_{number}.pdf"
            overlay_pdf = canvas.Canvas(str(stamp), pagesize=(page_width, page_height))
            overlay_pdf.setFont("Helvetica", 8)
            overlay_pdf.setFillColorRGB(0.25, 0.25, 0.25)
            overlay_pdf.drawCentredString(
                page_width / 2, 8 * mm, footer_text.format(page=number, total=total)
            )
            overlay_pdf.save()
            page.merge_page(pypdf.PdfReader(str(stamp)).pages[0])
        with open(output_pdf, "wb") as handle:
            writer.write(handle)
    finally:
        writer.close()
        shutil.rmtree(temp_dir, ignore_errors=True)


def compiler_make_excel(path: str | Path, title: str, case_info: str,
                        rows: Sequence[dict]) -> None:
    xlsxwriter = need("xlsxwriter")
    workbook = xlsxwriter.Workbook(str(path))
    try:
        index_sheet = workbook.add_worksheet("Master Index")
        checklist = workbook.add_worksheet("Compliance Checklist")
        title_format = workbook.add_format({
            "bold": True, "font_size": 15, "font_color": "white",
            "bg_color": "#17365D", "align": "center", "valign": "vcenter"
        })
        subtitle_format = workbook.add_format({
            "italic": True, "font_color": "#17365D", "bg_color": "#D9EAF7",
            "align": "center"
        })
        header_format = workbook.add_format({
            "bold": True, "font_color": "white", "bg_color": "#1F4E78",
            "border": 1, "align": "center", "valign": "vcenter", "text_wrap": True
        })
        cell_format = workbook.add_format({"border": 1, "valign": "top", "text_wrap": True})
        link_format = workbook.add_format({
            "border": 1, "font_color": "blue", "underline": True, "valign": "top"
        })
        index_sheet.merge_range("A1:J1", title, title_format)
        index_sheet.merge_range("A2:J2", case_info, subtitle_format)
        headings = [
            "Sr. No.", "Ground No.", "Issue", "Exhibit", "Particulars",
            "Paper Book Pages", "Original Pages", "Source PDF", "Remarks", "Status"
        ]
        index_sheet.write_row(3, 0, headings, header_format)
        for row_number, row in enumerate(rows, 4):
            values = [
                row["sr"], row["ground"], row["issue"], row["exhibit"],
                row["particulars"], row["pages"], row["source_pages"], "",
                row["remarks"], "Included"
            ]
            for column, value in enumerate(values):
                index_sheet.write(row_number, column, value, cell_format)
            try:
                index_sheet.write_url(
                    row_number, 7, "external:" + row["source"], link_format,
                    string=Path(row["source"]).name
                )
            except Exception:
                index_sheet.write(row_number, 7, Path(row["source"]).name, cell_format)
        index_sheet.set_column("A:A", 8)
        index_sheet.set_column("B:B", 12)
        index_sheet.set_column("C:C", 30)
        index_sheet.set_column("D:D", 10)
        index_sheet.set_column("E:E", 42)
        index_sheet.set_column("F:G", 16)
        index_sheet.set_column("H:H", 35)
        index_sheet.set_column("I:I", 30)
        index_sheet.set_column("J:J", 12)
        index_sheet.freeze_panes(4, 0)
        index_sheet.autofilter(3, 0, 3 + len(rows), 9)

        checklist.merge_range("A1:F1", "Hearing Notice Compliance Checklist", title_format)
        checklist.write_row(
            2, 0,
            ["Sr.", "Requirement", "Document / Exhibit", "Paper Book Pages", "Status", "Remarks"],
            header_format
        )
        requirements = [
            ("Grounds of Appeal", "Grounds of Appeal / relevant exhibit"),
            ("Ground-wise written submissions", "Written submissions mapped ground-wise"),
            ("Statement of Facts", "Statement of Facts"),
            ("Supporting documentary evidence", "Exhibits and supporting documents"),
            ("Case laws relied upon", "Case law compilation"),
            ("Electronic filing readiness", "Merged, paginated and indexed PDF"),
        ]
        for number, (requirement, document) in enumerate(requirements, 1):
            checklist.write_row(
                number + 2, 0, [number, requirement, document, "", "To verify", ""],
                cell_format
            )
        checklist.set_column("A:A", 8)
        checklist.set_column("B:B", 32)
        checklist.set_column("C:C", 38)
        checklist.set_column("D:D", 18)
        checklist.set_column("E:E", 14)
        checklist.set_column("F:F", 32)
    finally:
        workbook.close()


def prepare_paper_book_index(project: dict,
                             output_pdf: Optional[str | Path] = None) -> dict:
    """Calculate final paper-book ranges and optionally save a standalone PDF index."""
    documents = list(project.get("documents") or [])
    if not documents:
        raise FeatureError("Add at least one PDF document to the Compiler.")
    title = str(project.get("title") or "APPEAL PAPER BOOK")
    case_info = str(project.get("case_info") or "")
    for document in documents:
        source = Path(str(document.get("path") or ""))
        if not source.is_file():
            raise FeatureError(f"Source PDF not found: {source}")
        if source.suffix.lower() != ".pdf":
            raise FeatureError(f"Not a PDF file: {source.name}")
        compiler_page_count(source)

    temp_dir = Path(tempfile.mkdtemp(prefix="smartpdf_index_"))
    try:
        index_pdf = temp_dir / "master_index.pdf"
        index_pages = 1
        rows: list[dict] = []
        for _attempt in range(4):
            current_page = index_pages + 1
            rows = []
            for number, document in enumerate(documents, 1):
                source_pages = compiler_page_count(document["path"])
                divider_pages = 1 if document.get("divider", True) else 0
                start_page = current_page + divider_pages
                end_page = start_page + source_pages - 1
                rows.append({
                    "sr": number,
                    "exhibit": str(document.get("exhibit") or ""),
                    "particulars": str(
                        document.get("particulars") or Path(document["path"]).stem
                    ),
                    "ground": str(document.get("ground") or ""),
                    "issue": str(document.get("issue") or ""),
                    "pages": (
                        f"{start_page}-{end_page}" if start_page != end_page
                        else str(start_page)
                    ),
                    "source_pages": source_pages,
                    "source": str(document["path"]),
                    "remarks": str(document.get("remarks") or ""),
                })
                current_page = end_page + 1
            compiler_create_front_index(index_pdf, title, case_info, rows)
            actual_pages = compiler_page_count(index_pdf)
            if actual_pages == index_pages:
                break
            index_pages = actual_pages

        # One final render guarantees the displayed ranges use the settled index length.
        current_page = index_pages + 1
        rows = []
        for number, document in enumerate(documents, 1):
            source_pages = compiler_page_count(document["path"])
            divider_pages = 1 if document.get("divider", True) else 0
            start_page = current_page + divider_pages
            end_page = start_page + source_pages - 1
            rows.append({
                "sr": number,
                "exhibit": str(document.get("exhibit") or ""),
                "particulars": str(
                    document.get("particulars") or Path(document["path"]).stem
                ),
                "ground": str(document.get("ground") or ""),
                "issue": str(document.get("issue") or ""),
                "pages": (
                    f"{start_page}-{end_page}" if start_page != end_page
                    else str(start_page)
                ),
                "source_pages": source_pages,
                "source": str(document["path"]),
                "remarks": str(document.get("remarks") or ""),
            })
            current_page = end_page + 1
        compiler_create_front_index(index_pdf, title, case_info, rows)
        saved_output = ""
        if output_pdf is not None:
            target = Path(output_pdf).expanduser()
            target.parent.mkdir(parents=True, exist_ok=True)
            require_distinct_output(
                target, [str(document.get("path") or "") for document in documents]
            )
            shutil.copy2(index_pdf, target)
            saved_output = str(target)
        return {
            "output": saved_output, "rows": rows,
            "index_pages": compiler_page_count(index_pdf),
            "documents": len(documents), "title": title, "case_info": case_info,
        }
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)


def export_paper_book_index_excel(project: dict, output_excel: str | Path) -> dict:
    """Create the Excel master index and compliance checklist independently."""
    index_data = prepare_paper_book_index(project)
    target = Path(output_excel).expanduser()
    target.parent.mkdir(parents=True, exist_ok=True)
    compiler_make_excel(
        target, index_data["title"], index_data["case_info"], index_data["rows"]
    )
    return {
        "output": str(target), "rows": index_data["rows"],
        "documents": index_data["documents"],
    }


def compile_paper_book(project: dict, progress: Optional[Callable[[str], None]] = None) -> dict:
    documents = list(project.get("documents") or [])
    if not documents:
        raise FeatureError("Add at least one PDF document to the Compiler.")
    output_folder = Path(str(project.get("output_folder") or "")).expanduser()
    if not str(project.get("output_folder") or "").strip():
        raise FeatureError("Select an output folder.")
    output_folder.mkdir(parents=True, exist_ok=True)
    base_name = compiler_safe_filename(project.get("output_name") or "Appeal_Paper_Book")
    title = str(project.get("title") or "APPEAL PAPER BOOK")
    case_info = str(project.get("case_info") or "")
    for document in documents:
        source = Path(str(document.get("path") or ""))
        if not source.is_file():
            raise FeatureError(f"Source PDF not found: {source}")
        if source.suffix.lower() != ".pdf":
            raise FeatureError(f"Not a PDF file: {source.name}")
        compiler_page_count(source)
    final_pdf_path = output_folder / f"{base_name}.pdf"
    require_distinct_output(
        final_pdf_path, [str(document.get("path") or "") for document in documents]
    )

    pypdf = need("pypdf")
    temp_dir = Path(tempfile.mkdtemp(prefix="smartpdf_compiler_"))
    try:
        index_pages = 1
        rows: list[dict] = []
        for _attempt in range(4):
            current_page = index_pages + 1
            rows = []
            for number, document in enumerate(documents, 1):
                source_pages = compiler_page_count(document["path"])
                divider_pages = 1 if document.get("divider", True) else 0
                start_page = current_page + divider_pages
                end_page = start_page + source_pages - 1
                rows.append({
                    "sr": number,
                    "exhibit": str(document.get("exhibit") or ""),
                    "particulars": str(document.get("particulars") or Path(document["path"]).stem),
                    "ground": str(document.get("ground") or ""),
                    "issue": str(document.get("issue") or ""),
                    "pages": f"{start_page}-{end_page}" if start_page != end_page else str(start_page),
                    "source_pages": source_pages,
                    "source": str(document["path"]),
                    "remarks": str(document.get("remarks") or ""),
                })
                current_page = end_page + 1
            index_pdf = temp_dir / "master_index.pdf"
            compiler_create_front_index(index_pdf, title, case_info, rows)
            actual_index_pages = compiler_page_count(index_pdf)
            if actual_index_pages == index_pages:
                break
            index_pages = actual_index_pages

        # Recalculate once with the settled index length and render the exact index.
        current_page = index_pages + 1
        rows = []
        for number, document in enumerate(documents, 1):
            source_pages = compiler_page_count(document["path"])
            divider_pages = 1 if document.get("divider", True) else 0
            start_page = current_page + divider_pages
            end_page = start_page + source_pages - 1
            rows.append({
                "sr": number,
                "exhibit": str(document.get("exhibit") or ""),
                "particulars": str(document.get("particulars") or Path(document["path"]).stem),
                "ground": str(document.get("ground") or ""),
                "issue": str(document.get("issue") or ""),
                "pages": f"{start_page}-{end_page}" if start_page != end_page else str(start_page),
                "source_pages": source_pages,
                "source": str(document["path"]),
                "remarks": str(document.get("remarks") or ""),
            })
            current_page = end_page + 1
        index_pdf = temp_dir / "master_index.pdf"
        compiler_create_front_index(index_pdf, title, case_info, rows)

        writer = pypdf.PdfWriter()
        index_reader = pypdf.PdfReader(str(index_pdf), strict=False)
        for page in index_reader.pages:
            writer.add_page(page)
        bookmarks: list[tuple[str, int]] = []
        for number, (document, row) in enumerate(zip(documents, rows), 1):
            if progress:
                progress(f"Processing {number}/{len(documents)}: {Path(document['path']).name}")
            if document.get("divider", True):
                divider_pdf = temp_dir / f"divider_{number}.pdf"
                compiler_create_divider(
                    divider_pdf, str(document.get("exhibit") or ""), row["particulars"],
                    str(document.get("ground") or ""), str(document.get("issue") or "")
                )
                writer.add_page(pypdf.PdfReader(str(divider_pdf), strict=False).pages[0])
                bookmark_page = len(writer.pages) - 1
            else:
                bookmark_page = len(writer.pages)
            source_reader = pypdf.PdfReader(str(document["path"]), strict=False)
            if source_reader.is_encrypted:
                raise FeatureError(
                    f"Password-protected PDF is not supported: {Path(document['path']).name}"
                )
            for page in source_reader.pages:
                writer.add_page(page)
            bookmark_title = f"Exhibit {document.get('exhibit') or number} - {row['particulars']}"
            bookmarks.append((bookmark_title[:180], bookmark_page))
        merged_pdf = temp_dir / "merged.pdf"
        with open(merged_pdf, "wb") as handle:
            writer.write(handle)
        writer.close()

        merged_reader = pypdf.PdfReader(str(merged_pdf), strict=False)
        bookmarked_writer = pypdf.PdfWriter()
        for page in merged_reader.pages:
            bookmarked_writer.add_page(page)
        bookmarked_writer.add_outline_item("MASTER INDEX", 0)
        for bookmark_title, page_number in bookmarks:
            try:
                bookmarked_writer.add_outline_item(bookmark_title, page_number)
            except Exception:
                pass
        bookmarked_pdf = temp_dir / "bookmarked.pdf"
        with open(bookmarked_pdf, "wb") as handle:
            bookmarked_writer.write(handle)
        bookmarked_writer.close()

        if progress:
            progress("Adding continuous page numbers…")
        final_pdf = final_pdf_path
        compiler_stamp_page_numbers(bookmarked_pdf, final_pdf)
        if progress:
            progress("Creating Excel master index and compliance checklist…")
        final_excel = output_folder / f"{base_name}_Master_Index.xlsx"
        compiler_make_excel(final_excel, title, case_info, rows)
        project_file = output_folder / f"{base_name}_Project.apbc.json"
        project_file.write_text(json.dumps(project, indent=2), encoding="utf-8")
        total_pages = compiler_page_count(final_pdf)
        return {
            "pdf": str(final_pdf), "excel": str(final_excel),
            "project": str(project_file), "pages": total_pages,
            "documents": len(documents), "rows": rows,
        }
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)


# ---------------------------------------------------------------------------
# PDF Downloader — webpage discovery and safe local download
# ---------------------------------------------------------------------------


def _looks_like_pdf_url(url: str) -> bool:
    parsed = urlparse(url)
    path = unquote(parsed.path).casefold()
    query = unquote(parsed.query).casefold()
    return path.endswith(".pdf") or ".pdf&" in query or ".pdf=" in query or query.endswith(".pdf")


class PDFLinkHTMLParser(HTMLParser):
    """Collect PDF-capable links and embedded resources from an HTML page."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.candidates: list[tuple[str, bool]] = []
        self.base_href = ""
        self.active_anchor = ""

    def handle_starttag(self, tag: str, attrs: list[tuple[str, Optional[str]]]):
        values = {str(key).casefold(): (value or "") for key, value in attrs}
        tag = tag.casefold()
        if tag == "base" and values.get("href"):
            self.base_href = values["href"]
            return
        source = ""
        if tag in {"a", "link"}:
            source = values.get("href", "")
            if tag == "a":
                self.active_anchor = source
        elif tag in {"embed", "iframe", "source"}:
            source = values.get("src", "")
        elif tag == "object":
            source = values.get("data", "")
        if not source:
            return
        declared_pdf = "pdf" in values.get("type", "").casefold()
        declared_pdf = declared_pdf or "download" in values
        self.candidates.append((source, declared_pdf))

    def handle_data(self, data: str):
        if self.active_anchor and "pdf" in data.casefold():
            self.candidates.append((self.active_anchor, True))

    def handle_endtag(self, tag: str):
        if tag.casefold() == "a":
            self.active_anchor = ""


def normalize_webpage_url(value: str) -> str:
    url = value.strip()
    if not url:
        raise FeatureError("Enter a webpage URL.")
    if "://" not in url:
        url = "https://" + url
    parsed = urlparse(url)
    if parsed.scheme.casefold() not in {"http", "https"} or not parsed.netloc:
        raise FeatureError("Enter a valid http:// or https:// webpage URL.")
    return url


def discover_pdf_links(webpage_url: str,
                       log: Optional[Callable[[str], None]] = None) -> dict:
    url = normalize_webpage_url(webpage_url)
    if log:
        log(f"Opening webpage: {url}")
    request = Request(url, headers={
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) SmartPDFPro/4.5",
        "Accept": "text/html,application/xhtml+xml,application/pdf;q=0.9,*/*;q=0.8",
    })
    try:
        with urlopen(request, timeout=35) as response:
            final_url = response.geturl()
            content_type = (response.headers.get("Content-Type") or "").casefold()
            if "application/pdf" in content_type or _looks_like_pdf_url(final_url):
                if log:
                    log("The supplied URL is a direct PDF link.")
                return {"webpage": final_url, "links": [final_url], "direct": True}
            content_length = int(response.headers.get("Content-Length") or 0)
            if content_length > 20 * 1024 * 1024:
                raise FeatureError("The webpage is larger than the 20 MB scanning limit.")
            payload = response.read(20 * 1024 * 1024 + 1)
            if len(payload) > 20 * 1024 * 1024:
                raise FeatureError("The webpage is larger than the 20 MB scanning limit.")
            charset = response.headers.get_content_charset() or "utf-8"
    except HTTPError as exc:
        raise FeatureError(f"The webpage returned HTTP {exc.code}: {exc.reason}") from exc
    except URLError as exc:
        raise FeatureError(f"Could not open the webpage: {exc.reason}") from exc
    except TimeoutError as exc:
        raise FeatureError("The webpage took too long to respond.") from exc

    try:
        html = payload.decode(charset, errors="replace")
    except LookupError:
        html = payload.decode("utf-8", errors="replace")
    parser = PDFLinkHTMLParser()
    try:
        parser.feed(html)
    except Exception:
        # HTMLParser is forgiving, but retain already-discovered links if malformed markup fails.
        pass
    quoted_pdf_urls = re.findall(
        r'''["']([^"'<>\s]+?\.pdf(?:\?[^"'<>\s]*)?)["']''', html, flags=re.I
    )
    candidates = list(parser.candidates) + [(item, True) for item in quoted_pdf_urls]
    base_url = urljoin(final_url, parser.base_href) if parser.base_href else final_url
    links: list[str] = []
    seen: set[str] = set()
    for raw_url, declared_pdf in candidates:
        raw_url = raw_url.strip()
        if not raw_url or raw_url.casefold().startswith(("javascript:", "data:", "blob:", "mailto:")):
            continue
        absolute = urljoin(base_url, raw_url)
        parsed = urlparse(absolute)
        if parsed.scheme.casefold() not in {"http", "https"}:
            continue
        absolute = absolute.split("#", 1)[0]
        if not (declared_pdf or _looks_like_pdf_url(absolute)):
            continue
        key = absolute.casefold()
        if key not in seen:
            seen.add(key)
            links.append(absolute)
    if log:
        log(f"Scan complete: {len(links)} PDF link(s) found.")
    return {"webpage": final_url, "links": links, "direct": False}


def _download_filename(url: str, content_disposition: str, number: int) -> str:
    filename = ""
    encoded = re.search(r"filename\*\s*=\s*(?:UTF-8'')?([^;]+)", content_disposition, re.I)
    ordinary = re.search(r'filename\s*=\s*["\']?([^"\';]+)', content_disposition, re.I)
    if encoded:
        filename = unquote(encoded.group(1).strip().strip('"\''))
    elif ordinary:
        filename = ordinary.group(1).strip()
    if not filename:
        filename = unquote(Path(urlparse(url).path).name)
    if not filename or filename in {"/", "."}:
        filename = f"document_{number:03d}.pdf"
    filename = safe_filename(filename, f"document_{number:03d}")
    if not filename.casefold().endswith(".pdf"):
        filename += ".pdf"
    return filename


def download_pdf_links(links: Sequence[str], output_folder: str,
                       progress: Optional[Callable[[int, int, str], None]] = None,
                       log: Optional[Callable[[str], None]] = None,
                       referer: Optional[str] = None) -> dict:
    if not links:
        raise FeatureError("Scan a webpage and find at least one PDF link first.")
    require_network("Downloading PDFs")
    destination = Path(output_folder).expanduser()
    destination.mkdir(parents=True, exist_ok=True)
    downloaded: list[str] = []
    failed: list[tuple[str, str]] = []
    total = len(links)
    for number, url in enumerate(links, 1):
        if progress:
            progress(number - 1, total, f"Downloading {number} of {total}…")
        if log:
            log(f"Downloading {number}/{total}: {url}")
        partial: Optional[Path] = None
        try:
            request = Request(url, headers={
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) SmartPDFPro/4.5",
                "Accept": "application/pdf,*/*;q=0.8",
                "Referer": referer or url,
            })
            with urlopen(request, timeout=60) as response:
                content_type = (response.headers.get("Content-Type") or "").casefold()
                content_length = int(response.headers.get("Content-Length") or 0)
                if content_length > MAX_FILE_BYTES:
                    raise FeatureError("File exceeds the 500 MB download limit.")
                if response.status and int(response.status) >= 400:
                    raise FeatureError(
                        f"The server replied {response.status} for this link."
                    )
                filename = _download_filename(
                    response.geturl(), response.headers.get("Content-Disposition") or "", number
                )
                output_path = unique_path(destination / filename)
                partial = destination / f".{uuid.uuid4().hex}.part"
                written = 0
                first_chunk = True
                with open(partial, "wb") as handle:
                    while True:
                        chunk = response.read(128 * 1024)
                        if not chunk:
                            break
                        if first_chunk:
                            first_chunk = False
                            if "application/pdf" not in content_type and not chunk.lstrip().startswith(b"%PDF-"):
                                head = chunk[:120].decode("utf-8", "replace").strip()
                                raise FeatureError(
                                    "This link did not return a PDF.\n"
                                    f"Server sent '{content_type or 'unknown type'}'.\n"
                                    "It is usually a login page, a redirect, or a viewer "
                                    "page rather than the file itself. Open the link in a "
                                    "browser and copy the direct .pdf address.\n"
                                    f"First bytes: {head[:70]}"
                                )
                        written += len(chunk)
                        if written > MAX_FILE_BYTES:
                            raise FeatureError("File exceeds the 500 MB download limit.")
                        handle.write(chunk)
                if written == 0:
                    raise FeatureError("The server returned an empty file.")
                os.replace(partial, output_path)
                partial = None
                downloaded.append(str(output_path))
                if log:
                    log(f"Saved: {output_path.name} ({human_size(written)})")
        except Exception as exc:
            if partial and partial.exists():
                try:
                    partial.unlink()
                except OSError:
                    pass
            detail = str(exc).strip() or exc.__class__.__name__
            failed.append((url, detail))
            if log:
                log(f"Failed: {detail}")
        if progress:
            progress(number, total, f"Processed {number} of {total}")
    return {
        "downloaded": downloaded, "failed": failed, "folder": str(destination),
        "total": total,
    }


def split_pdf(input_path: str, output_dir: str, mode: str, value: str) -> dict:
    pypdf = need("pypdf")
    check_size(input_path)
    reader = pypdf.PdfReader(input_path)
    if reader.is_encrypted:
        raise FeatureError("This PDF is password-protected.")
    total = len(reader.pages)
    if total == 0:
        raise FeatureError("The selected PDF has no pages.")

    if mode == "Every page":
        groups = [[i] for i in range(total)]
    elif mode == "Every N pages":
        try:
            n = int(value)
        except ValueError as exc:
            raise FeatureError("Enter a valid number of pages per file.") from exc
        if n < 1:
            raise FeatureError("Pages per file must be at least 1.")
        groups = [list(range(i, min(i + n, total))) for i in range(0, total, n)]
    elif mode == "Equal parts":
        try:
            parts = int(value)
        except ValueError as exc:
            raise FeatureError("Enter a valid number of parts.") from exc
        if parts < 1 or parts > total:
            raise FeatureError(f"Parts must be between 1 and {total}.")
        base, extra = divmod(total, parts)
        groups, cursor = [], 0
        for idx in range(parts):
            length = base + (1 if idx < extra else 0)
            groups.append(list(range(cursor, cursor + length)))
            cursor += length
    elif mode == "Selected pages (one PDF)":
        groups = [parse_pages(value, total)]
    elif mode == "Custom groups":
        groups = parse_groups(value, total)
    else:
        raise FeatureError(f"Unknown split mode: {mode}")

    destination = Path(output_dir)
    destination.mkdir(parents=True, exist_ok=True)
    stem = safe_filename(Path(input_path).stem)
    outputs: list[str] = []
    for number, group in enumerate(groups, start=1):
        writer = pypdf.PdfWriter()
        try:
            for page_index in group:
                writer.add_page(reader.pages[page_index])
            first, last = group[0] + 1, group[-1] + 1
            label = f"page_{first}" if first == last else f"pages_{first}-{last}"
            out = unique_path(destination / f"{stem}_{number:03d}_{label}.pdf")
            with open(out, "wb") as handle:
                writer.write(handle)
            outputs.append(str(out))
        finally:
            writer.close()
    return {"outputs": outputs, "count": len(outputs), "folder": str(destination)}


def organize_pdf(input_path: str, output: str, plan: Sequence[tuple[int, int]]) -> dict:
    """plan contains (zero-based source page, clockwise rotation degrees)."""
    require_distinct_output(output, (input_path,))
    pypdf = need("pypdf")
    reader = pypdf.PdfReader(input_path)
    if reader.is_encrypted:
        raise FeatureError("This PDF is password-protected.")
    if not plan:
        raise FeatureError("At least one page must remain in the document.")
    writer = pypdf.PdfWriter()
    try:
        for source_index, rotation in plan:
            page = reader.pages[source_index]
            if rotation % 360:
                page.rotate(rotation % 360)
            writer.add_page(page)
        with open(output, "wb") as handle:
            writer.write(handle)
    finally:
        writer.close()
    return {"output": output, "pages": len(plan)}


POSITIONS = {
    "Top left": (0.08, 0.10),
    "Top centre": (0.50, 0.10),
    "Top right": (0.92, 0.10),
    "Centre left": (0.08, 0.50),
    "Centre": (0.50, 0.50),
    "Centre right": (0.92, 0.50),
    "Bottom left": (0.08, 0.90),
    "Bottom centre": (0.50, 0.90),
    "Bottom right": (0.92, 0.90),
}


def _font_path() -> Optional[str]:
    candidates = [
        r"C:\Windows\Fonts\arial.ttf",
        "/System/Library/Fonts/Supplemental/Arial.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ]
    return next((p for p in candidates if Path(p).exists()), None)


def _text_watermark_png(text: str, size: int, opacity: float, rotation: float) -> bytes:
    need("PIL", "pillow")
    from PIL import Image, ImageDraw, ImageFont

    font_path = _font_path()
    font = ImageFont.truetype(font_path, max(10, size)) if font_path else ImageFont.load_default()
    scratch = Image.new("RGBA", (16, 16), (0, 0, 0, 0))
    draw = ImageDraw.Draw(scratch)
    bbox = draw.textbbox((0, 0), text, font=font, stroke_width=1)
    width = max(10, bbox[2] - bbox[0] + 20)
    height = max(10, bbox[3] - bbox[1] + 20)
    image = Image.new("RGBA", (width, height), (0, 0, 0, 0))
    draw = ImageDraw.Draw(image)
    alpha = max(0, min(255, int(opacity * 255)))
    draw.text((10 - bbox[0], 10 - bbox[1]), text, font=font, fill=(34, 82, 126, alpha))
    if rotation % 360:
        image = image.rotate(rotation, expand=True, resample=Image.Resampling.BICUBIC)
    buffer = io.BytesIO()
    image.save(buffer, format="PNG")
    return buffer.getvalue()


def _image_watermark_png(path: str, opacity: float, rotation: float) -> tuple[bytes, float]:
    need("PIL", "pillow")
    from PIL import Image

    with Image.open(path) as source:
        image = source.convert("RGBA")
        alpha = image.getchannel("A").point(lambda p: int(p * max(0.0, min(1.0, opacity))))
        image.putalpha(alpha)
        ratio = image.height / max(1, image.width)
        if rotation % 360:
            image = image.rotate(rotation, expand=True, resample=Image.Resampling.BICUBIC)
            ratio = image.height / max(1, image.width)
        buffer = io.BytesIO()
        image.save(buffer, format="PNG")
    return buffer.getvalue(), ratio


def add_watermark(
    input_path: str,
    output: str,
    kind: str,
    content: str,
    pages_text: str,
    position: str,
    opacity: float,
    rotation: float,
    size: float,
    tiled: bool,
) -> dict:
    require_distinct_output(output, (input_path,))
    pymupdf = get_pymupdf()
    check_size(input_path)
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected.")
    target_pages = parse_pages(pages_text, doc.page_count)
    if kind == "Text":
        if not content.strip():
            doc.close()
            raise FeatureError("Enter watermark text.")
        png = _text_watermark_png(content.strip(), int(size), opacity, rotation)
        # Pillow already sizes the text; use a sensible PDF point width.
        aspect = None
    else:
        if not content or not Path(content).is_file():
            doc.close()
            raise FeatureError("Select a PNG or JPEG watermark image.")
        png, aspect = _image_watermark_png(content, opacity, rotation)

    try:
        for page_index in target_pages:
            page = doc[page_index]
            page_w, page_h = page.rect.width, page.rect.height
            if kind == "Text":
                # Approximate width based on font size and text length.
                mark_w = min(page_w * 0.85, max(size * 2.0, len(content) * size * 0.58))
                mark_h = max(size * 1.5, mark_w * 0.18)
            else:
                mark_w = page_w * max(0.05, min(0.9, size / 100.0))
                mark_h = mark_w * float(aspect or 0.5)

            def place(cx: float, cy: float) -> None:
                left = max(0.0, min(page_w - mark_w, page_w * cx - mark_w / 2))
                top = max(0.0, min(page_h - mark_h, page_h * cy - mark_h / 2))
                page.insert_image(
                    pymupdf.Rect(left, top, left + mark_w, top + mark_h),
                    stream=png,
                    overlay=True,
                    keep_proportion=True,
                )

            if tiled:
                step_x = max(mark_w * 1.45, page_w * 0.22)
                step_y = max(mark_h * 2.2, page_h * 0.18)
                y = step_y / 2
                row = 0
                while y < page_h:
                    x = step_x / 2 + (step_x / 2 if row % 2 else 0)
                    while x < page_w:
                        place(x / page_w, y / page_h)
                        x += step_x
                    y += step_y
                    row += 1
            else:
                place(*POSITIONS.get(position, POSITIONS["Centre"]))
        doc.save(output, garbage=4, deflate=True, clean=True)
    finally:
        doc.close()
    return {"output": output, "pages": len(target_pages)}


# ---------------------------------------------------------------------------
# Local settings persistence (used by licensing and other app preferences)
# ---------------------------------------------------------------------------

CONFIG_PATH = Path.home() / ".smart_pdf_pro.json"


def load_settings() -> dict:
    """Read persisted app settings; never raises."""
    try:
        if CONFIG_PATH.is_file():
            return json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
    except Exception:
        pass
    return {}


def save_settings(data: dict) -> None:
    """Merge and persist app settings; never raises."""
    try:
        merged = load_settings()
        merged.update(data)
        CONFIG_PATH.write_text(json.dumps(merged, indent=2), encoding="utf-8")
    except Exception:
        pass


# ---------------------------------------------------------------------------
# LICENSING — offline-validated keys, 180-day trial, 365-day activation
# ---------------------------------------------------------------------------
#
# Design notes (so future maintainers understand the trade-offs):
#
# This is a single-file desktop app with no license server. Keys are
# validated ENTIRELY OFFLINE using an embedded HMAC secret: a key is only
# "valid" if its checksum matches what that secret would produce for its
# body. This lets 1000 keys be pre-generated and handed to customers, and
# lets the app validate any of them (or reject a typo/forgery) without ever
# phoning home.
#
# This is NOT tamper-proof — anyone with the source can read the secret and
# mint their own keys. That is an inherent limitation of client-side
# licensing with no server; it deters casual copying and lets legitimate
# customers self-activate, which is what was asked for.

LICENSE_SECRET = b"TaxOSmart-SmartPDFPro-2026-9f3a7c1e-LicenseSigningKey"
LICENSE_BODY_LEN = 15          # random, human-typed portion
LICENSE_CHECK_LEN = 10         # HMAC-derived checksum portion
LICENSE_TOTAL_LEN = LICENSE_BODY_LEN + LICENSE_CHECK_LEN  # 25 characters
LICENSE_ALPHABET = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"  # no 0/O/1/I — avoids confusion

TRIAL_DAYS = 180
LICENSE_VALIDITY_DAYS = 365


def _license_checksum(body: str) -> str:
    """Derive a fixed-length checksum for a key body using the embedded secret."""
    digest = hmac.new(LICENSE_SECRET, body.encode("ascii"), hashlib.sha256).digest()
    # Map digest bytes onto the restricted alphabet so the whole key stays
    # easy to read and type (no lookalike characters, one case only).
    chars = []
    for byte in digest:
        chars.append(LICENSE_ALPHABET[byte % len(LICENSE_ALPHABET)])
        if len(chars) >= LICENSE_CHECK_LEN:
            break
    return "".join(chars)


def generate_license_key() -> str:
    """Generate one valid 25-character license key (no formatting dashes)."""
    body = "".join(secrets.choice(LICENSE_ALPHABET) for _ in range(LICENSE_BODY_LEN))
    return body + _license_checksum(body)


def format_license_key(key: str) -> str:
    """Group a raw key into 5-character blocks for display: AAAAA-BBBBB-..."""
    clean = normalize_license_key(key)
    return "-".join(clean[i:i + 5] for i in range(0, len(clean), 5))


def normalize_license_key(key: str) -> str:
    """Strip whitespace/dashes and uppercase, for both storage and comparison."""
    return "".join(ch for ch in key.upper() if ch.isalnum())


def validate_license_key(key: str) -> bool:
    """True if a key's checksum matches what the embedded secret would produce."""
    clean = normalize_license_key(key)
    if len(clean) != LICENSE_TOTAL_LEN:
        return False
    body, checksum = clean[:LICENSE_BODY_LEN], clean[LICENSE_BODY_LEN:]
    if any(ch not in LICENSE_ALPHABET for ch in clean):
        return False
    return hmac.compare_digest(_license_checksum(body), checksum)


def generate_license_batch(count: int) -> list[str]:
    """Generate `count` unique, valid license keys."""
    seen: set[str] = set()
    keys: list[str] = []
    while len(keys) < count:
        key = generate_license_key()
        if key not in seen:
            seen.add(key)
            keys.append(key)
    return keys


def _license_state() -> dict:
    return load_settings().get("license", {}) or {}


def _save_license_state(state: dict) -> None:
    save_settings({"license": state})


def get_install_date() -> str:
    """Return (and persist, on first call) the date this copy was first run."""
    state = _license_state()
    install_date = state.get("install_date")
    if not install_date:
        install_date = date.today().isoformat()
        state["install_date"] = install_date
        _save_license_state(state)
    return install_date


def days_since(iso_date: str) -> int:
    try:
        then = date.fromisoformat(iso_date)
    except Exception:
        return 0
    return max(0, (date.today() - then).days)


def activate_license(raw_key: str) -> dict:
    """Validate and store a license key. Raises FeatureError if invalid."""
    if not validate_license_key(raw_key):
        raise FeatureError(
            "This license key is not valid.\n\n"
            "Check that all 25 characters were entered correctly — the letters "
            "0, O, 1 and I are never used in a genuine key, to avoid confusion."
        )
    clean = normalize_license_key(raw_key)
    state = _license_state()
    state["license_key"] = clean
    state["activated_on"] = date.today().isoformat()
    _save_license_state(state)
    return get_license_status()


def deactivate_license() -> None:
    state = _license_state()
    state.pop("license_key", None)
    state.pop("activated_on", None)
    _save_license_state(state)


def get_license_status() -> dict:
    """Return the full licensing picture: trial and/or paid activation state.

    Keys in the result:
      mode            "licensed" | "trial" | "expired"
      allowed         bool — whether the app should let the user work
      days_remaining  int
      license_key     formatted key, or None
      trial_days_left int
    """
    install_date = get_install_date()
    trial_used = days_since(install_date)
    trial_days_left = max(0, TRIAL_DAYS - trial_used)

    state = _license_state()
    key = state.get("license_key")
    activated_on = state.get("activated_on")

    if key and validate_license_key(key) and activated_on:
        used = days_since(activated_on)
        remaining = LICENSE_VALIDITY_DAYS - used
        if remaining > 0:
            return {
                "mode": "licensed",
                "allowed": True,
                "days_remaining": remaining,
                "license_key": format_license_key(key),
                "trial_days_left": trial_days_left,
            }
        # License lapsed after its 365-day validity window
        return {
            "mode": "expired",
            "allowed": trial_days_left > 0,
            "days_remaining": 0,
            "license_key": format_license_key(key),
            "trial_days_left": trial_days_left,
        }

    if trial_days_left > 0:
        return {
            "mode": "trial",
            "allowed": True,
            "days_remaining": trial_days_left,
            "license_key": None,
            "trial_days_left": trial_days_left,
        }

    return {
        "mode": "expired",
        "allowed": False,
        "days_remaining": 0,
        "license_key": None,
        "trial_days_left": 0,
    }


def pdf_needs_ocr(path: str) -> bool:
    pymupdf = get_pymupdf()
    doc = pymupdf.open(path)
    try:
        return not any(doc[i].get_text().strip() for i in range(min(doc.page_count, 5)))
    finally:
        doc.close()


def find_tesseract_executable(custom_path: Optional[str] = None) -> Optional[str]:
    """Find the OCR engine in PATH, common install folders, or a user-selected path."""
    # Accept either the complete tesseract.exe path or its installation folder.
    custom_executable: Optional[str] = None
    if custom_path:
        supplied_path = Path(custom_path).expanduser()
        custom_executable = str(
            supplied_path / "tesseract.exe" if supplied_path.is_dir() else supplied_path
        )

    candidates: list[Optional[str]] = [
        custom_executable,
        shutil.which("tesseract"),
        r"C:\Users\RJSA-L12\AppData\Local\Tesseract-OCR\tesseract.exe",
        str(Path(__file__).resolve().parent / "tesseract.exe"),
        str(Path(__file__).resolve().parent / "Tesseract-OCR" / "tesseract.exe"),
    ]
    for variable, suffix in (
        ("ProgramFiles", ("Tesseract-OCR", "tesseract.exe")),
        ("ProgramFiles(x86)", ("Tesseract-OCR", "tesseract.exe")),
        ("LOCALAPPDATA", ("Tesseract-OCR", "tesseract.exe")),
        ("LOCALAPPDATA", ("Programs", "Tesseract-OCR", "tesseract.exe")),
        ("USERPROFILE", ("scoop", "apps", "tesseract", "current", "tesseract.exe")),
    ):
        base = os.environ.get(variable)
        if base:
            candidates.append(str(Path(base).joinpath(*suffix)))
    for candidate in candidates:
        if candidate and Path(candidate).is_file():
            return str(Path(candidate).resolve())
    return None


def configure_tesseract(custom_path: Optional[str] = None) -> str:
    need("pytesseract")
    import pytesseract

    executable = find_tesseract_executable(custom_path)
    if not executable:
        raise FeatureError(
            "Tesseract OCR engine was not found.\n\n"
            "If the PDF contains selectable text, clear 'Use OCR' and translate again.\n\n"
            "For a scanned PDF on Windows:\n"
            "1. Install Tesseract OCR.\n"
            "2. Include the required language data during installation.\n"
            "3. Use 'Locate Tesseract' in the Translate screen and select tesseract.exe."
        )
    pytesseract.pytesseract.tesseract_cmd = executable
    try:
        pytesseract.get_tesseract_version()
    except Exception as exc:
        raise FeatureError(
            f"Tesseract was found but could not be started:\n{executable}\n\n{str(exc)[:220]}"
        ) from exc
    return executable


def get_available_tesseract_langs(tesseract_path: Optional[str] = None) -> list[str]:
    """Return a sorted list of installed Tesseract language codes (e.g. ['eng','hin','guj'])."""
    try:
        need("pytesseract")
        import pytesseract
        executable = find_tesseract_executable(tesseract_path)
        if not executable:
            return []
        pytesseract.pytesseract.tesseract_cmd = executable
        langs = pytesseract.get_languages(config="")
        return sorted(lang for lang in langs if lang and lang != "osd")
    except Exception:
        return []


# Human-readable names for Tesseract language codes (for error messages)
TESSERACT_LANG_NAMES = {
    "eng": "English",       "hin": "Hindi",       "mar": "Marathi",
    "guj": "Gujarati",      "ben": "Bengali",      "tam": "Tamil",
    "tel": "Telugu",        "kan": "Kannada",      "mal": "Malayalam",
    "pan": "Punjabi",       "urd": "Urdu",         "asm": "Assamese",
    "ori": "Odia",          "san": "Sanskrit",     "nep": "Nepali",
    "ara": "Arabic",        "fra": "French",       "deu": "German",
    "spa": "Spanish",       "jpn": "Japanese",     "chi_sim": "Chinese (Simplified)",
}

# Windows installer download URLs per language pack
TESSERACT_PACK_URL = (
    "https://github.com/UB-Mannheim/tesseract/wiki\n"
    "  → During install, expand 'Additional language data' and tick the required language."
)


def ocr_pdf_text(
    path: str, language: str = "eng", tesseract_path: Optional[str] = None
) -> Iterable[tuple[int, str]]:
    pymupdf = get_pymupdf()
    need("pytesseract")
    need("PIL", "pillow")
    import pytesseract
    from PIL import Image

    configure_tesseract(tesseract_path)

    doc = pymupdf.open(path)
    try:
        for index, page in enumerate(doc, start=1):
            pix = page.get_pixmap(dpi=200, alpha=False)
            image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
            try:
                text = pytesseract.image_to_string(
                    image, lang=language, config="-c preserve_interword_spaces=1"
                ) or ""
            except pytesseract.TesseractNotFoundError as exc:
                raise FeatureError(
                    "Tesseract OCR could not be started. Use 'Locate Tesseract' and select tesseract.exe."
                ) from exc
            except pytesseract.TesseractError as exc:
                lang_name = TESSERACT_LANG_NAMES.get(language, language)
                installed = get_available_tesseract_langs(tesseract_path)
                installed_str = (
                    "Installed packs: " + ", ".join(installed)
                    if installed else "No language packs detected."
                )
                raise FeatureError(
                    f"Tesseract does not have the '{language}' ({lang_name}) language pack.\n\n"
                    f"{installed_str}\n\n"
                    "HOW TO FIX (choose one):\n"
                    "  1. Re-run the Tesseract installer and tick the missing language pack:\n"
                    "     https://github.com/UB-Mannheim/tesseract/wiki\n"
                    "     Expand 'Additional language data' during install.\n\n"
                    f"  2. Download only the missing file ({language}.traineddata):\n"
                    f"     https://github.com/tesseract-ocr/tessdata/raw/main/{language}.traineddata\n"
                    "     Save it to: C:\\Program Files\\Tesseract-OCR\\tessdata\\\n\n"
                    "  3. Change 'Source language' to 'Auto detect' or 'English' if your\n"
                    "     PDF already has selectable text (OCR may not be needed at all)."
                ) from exc
            yield index, text
    finally:
        doc.close()


def extract_pdf_text_pages(
    input_path: str,
    use_ocr: bool = False,
    source_language: str = "auto",
    tesseract_path: Optional[str] = None,
) -> list[str]:
    """Extract one text string per source page, using OCR when requested/needed."""
    check_size(input_path)
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected.")
    try:
        extracted = [page.get_text("text", sort=True).strip() for page in doc]
    finally:
        doc.close()
    has_embedded_text = any(text for text in extracted)
    should_ocr = use_ocr or not has_embedded_text
    if should_ocr:
        tess_code = TESSERACT_LANGUAGES.get(source_language, "eng")
        try:
            configure_tesseract(tesseract_path)
        except FeatureError:
            # If the PDF has embedded/selectable text, skip OCR silently.
            # Only raise if the PDF is genuinely scanned with no text layer.
            if has_embedded_text:
                return extracted
            # For truly scanned PDFs, re-raise with a clear, friendly message.
            raise FeatureError(
                "This appears to be a scanned PDF and Tesseract OCR was not found.\n\n"
                "For selectable-text PDFs: uncheck 'Use OCR' and try again.\n\n"
                "For scanned PDFs, install Tesseract OCR:\n"
                "  Windows: https://github.com/UB-Mannheim/tesseract/wiki\n"
                "  macOS:   brew install tesseract\n"
                "  Linux:   sudo apt install tesseract-ocr\n\n"
                "After installation, use 'Locate Tesseract' in the Translate screen."
            )
        extracted = [
            text.strip()
            for _page, text in ocr_pdf_text(input_path, tess_code, tesseract_path)
        ]
    if not any(extracted):
        raise FeatureError(
            "No readable text was found. Enable OCR and ensure the required Tesseract language pack is installed."
        )
    return extracted


def _translation_chunks(text: str, limit: int = 3500) -> list[str]:
    """Split long page text without cutting words or paragraphs where practical."""
    normalized = re.sub(r"\r\n?", "\n", text).strip()
    if not normalized:
        return []
    paragraphs = [part.strip() for part in re.split(r"\n\s*\n", normalized) if part.strip()]
    chunks: list[str] = []
    current = ""
    for paragraph in paragraphs:
        pieces = [paragraph]
        if len(paragraph) > limit:
            pieces = []
            remainder = paragraph
            while len(remainder) > limit:
                cut = remainder.rfind(" ", 0, limit)
                if cut < limit // 2:
                    cut = limit
                pieces.append(remainder[:cut].strip())
                remainder = remainder[cut:].strip()
            if remainder:
                pieces.append(remainder)
        for piece in pieces:
            proposed = f"{current}\n\n{piece}".strip() if current else piece
            if current and len(proposed) > limit:
                chunks.append(current)
                current = piece
            else:
                current = proposed
    if current:
        chunks.append(current)
    return chunks


def detect_language_code(text: str) -> str:
    need("langdetect")
    from langdetect import DetectorFactory, detect

    DetectorFactory.seed = 0
    sample = re.sub(r"\s+", " ", text).strip()[:5000]
    if len(sample) < 12:
        raise FeatureError("There is not enough text to detect the source language reliably.")
    try:
        detected = detect(sample)
    except Exception as exc:
        raise FeatureError("Automatic source-language detection failed. Select the language manually.") from exc
    normalised = {"zh-cn": "zh-CN", "zh-tw": "zh-CN"}.get(detected.lower(), detected.lower())
    if normalised not in set(LANGUAGES.values()):
        raise FeatureError(
            f"Detected language code '{detected}' is not in the current language list. "
            "Select the source language manually."
        )
    return normalised


def translate_text_online(text: str, source_code: str, target_code: str) -> str:
    """Online translation via Google Translate, falling back to MyMemory. Requires internet."""
    need("deep_translator", "deep-translator")
    from deep_translator import GoogleTranslator, MyMemoryTranslator

    if source_code == target_code and source_code != "auto":
        return text
    google = GoogleTranslator(source=source_code, target=target_code)
    translated: list[str] = []
    for chunk in _translation_chunks(text):
        try:
            value = google.translate(chunk)
        except Exception as google_error:
            source_memory = MYMEMORY_LANGUAGES.get(source_code)
            target_memory = MYMEMORY_LANGUAGES.get(target_code)
            if not source_memory or not target_memory:
                raise FeatureError(
                    "The primary translation provider did not return a result and the fallback "
                    "provider does not support this language pair.\n\n"
                    f"Details: {str(google_error)[:220]}"
                ) from google_error
            fallback_parts: list[str] = []
            try:
                fallback = MyMemoryTranslator(source=source_memory, target=target_memory)
                for piece in _translation_chunks(chunk, limit=450):
                    fallback_parts.append(fallback.translate(piece) or "")
                value = "\n\n".join(fallback_parts)
            except Exception as fallback_error:
                raise FeatureError(
                    "Both translation providers failed. Check the internet connection, "
                    "language selection, and provider availability.\n\n"
                    f"Primary: {str(google_error)[:130]}\nFallback: {str(fallback_error)[:130]}"
                ) from fallback_error
        translated.append(value or "")
    return "\n\n".join(translated).strip()


# ---------------------------------------------------------------------------
# Offline translation — Argos Translate (fully local, no internet at runtime)
# ---------------------------------------------------------------------------

# Argos Translate only ships models for these languages (paired through English).
# This is a hard limitation of the offline engine, not of this app.
ARGOS_LANGUAGES = {
    "auto": "auto", "en": "en", "hi": "hi", "bn": "bn", "ur": "ur",
    "ar": "ar", "zh-CN": "zh", "ja": "ja", "fr": "fr", "de": "de", "es": "es",
}
ARGOS_UNSUPPORTED_NOTE = (
    "Argos Translate (offline engine) does not currently provide language packs for: "
    "Marathi, Gujarati, Tamil, Telugu, Kannada, Malayalam, Punjabi, Odia, Assamese, "
    "Sanskrit, Nepali. Use the Online engine for these languages, or check back after "
    "an Argos Translate update."
)


def _module_available(module_name: str) -> bool:
    """True if an optional dependency can be imported, without raising."""
    try:
        import importlib
        importlib.import_module(module_name)
        return True
    except Exception:
        return False


def argos_is_language_supported(app_lang_code: str) -> bool:
    return app_lang_code in ARGOS_LANGUAGES


def _argos_installed_pairs() -> set[tuple[str, str]]:
    need("argostranslate", "argostranslate")
    import argostranslate.translate as argos_translate

    pairs = set()
    for lang in argos_translate.get_installed_languages():
        for target in lang.translations_to:
            pairs.add((lang.code, target.to_lang.code))
    return pairs


def argos_installed_language_codes() -> set[str]:
    """App-facing language codes (en, hi, bn, ...) that have at least one installed
    pack in either direction with English. Used to show install status in the UI."""
    installed = set()
    try:
        pairs = _argos_installed_pairs()
    except FeatureError:
        return installed
    for from_code, to_code in pairs:
        if from_code == "en":
            installed.add(to_code)
        if to_code == "en":
            installed.add(from_code)
    installed.discard("en")
    return installed


def argos_pair_ready(source_code: str, target_code: str) -> tuple[bool, str]:
    """Truthfully report whether an offline translation can be performed.

    Returns (ready, human_readable_reason). Unlike a naive check, this never
    reports 'ready' just because English is involved — an actual installed
    package is always required.
    """
    argos_source = ARGOS_LANGUAGES.get(source_code)
    argos_target = ARGOS_LANGUAGES.get(target_code)
    if argos_target is None or argos_source is None:
        return False, "This language is not available in the offline engine."
    if argos_source != "auto" and argos_source == argos_target:
        return True, "Source and target are the same; no translation needed."

    try:
        pairs = _argos_installed_pairs()
    except Exception:
        pairs = set()
    if not pairs:
        return False, "No offline language packs are installed yet."

    def leg(a: str, b: str) -> bool:
        return a == b or (a, b) in pairs

    def path_ok(a: str, b: str) -> bool:
        # Direct pack, or pivot through English (Argos ships X<->en packs)
        return leg(a, b) or (leg(a, "en") and leg("en", b))

    if argos_source == "auto":
        # Auto-detect could yield any language, so require at least one
        # installed source that can reach the target.
        sources = {f for f, _ in pairs} | {"en"}
        usable = sorted(s for s in sources if s != argos_target and path_ok(s, argos_target))
        if usable:
            return True, f"Auto-detect can reach the target from: {', '.join(usable)}"
        return False, f"No installed pack can translate into '{argos_target}'."

    if path_ok(argos_source, argos_target):
        return True, f"Pack available for {argos_source} \u2192 {argos_target}."
    missing = []
    if not leg(argos_source, "en"):
        missing.append(f"{argos_source}\u2192en")
    if not leg("en", argos_target):
        missing.append(f"en\u2192{argos_target}")
    return False, "Missing pack(s): " + ", ".join(missing or [f"{argos_source}\u2192{argos_target}"])


def argos_install_from_file(file_path: str) -> dict:
    """Install an already-downloaded .argosmodel file (no internet needed for this step).
    Use this when the pack was downloaded manually — e.g. via a browser on a machine
    where the app's own download failed because of a firewall/proxy."""
    need("argostranslate", "argostranslate")
    import argostranslate.package as argos_package

    path = Path(file_path)
    if not path.is_file():
        raise FeatureError(f"File not found:\n{file_path}")
    if path.suffix.casefold() != ".argosmodel":
        raise FeatureError(
            f"'{path.name}' does not look like an Argos Translate package.\n\n"
            "The file must end in .argosmodel (not .zip, .argosmodel.zip, or a "
            "partial download such as .crdownload/.part). Re-download it and make "
            "sure the download finished completely before installing."
        )
    if path.stat().st_size < 1024:
        raise FeatureError(
            f"'{path.name}' is only {path.stat().st_size} bytes — this looks like an "
            "incomplete or failed download, not a real language pack. Re-download the file."
        )
    before = argos_installed_language_codes()
    try:
        argos_package.install_from_path(str(path))
    except Exception as exc:
        raise FeatureError(
            f"Could not install '{path.name}'. The file may be corrupted or incomplete.\n\n"
            f"Details: {str(exc)[:220]}"
        ) from exc
    # install_from_path() can silently no-op on a malformed archive (e.g. one that was
    # re-zipped without its internal package folder) — it raises no error but never
    # actually registers the language. Confirm something new actually appeared.
    after = argos_installed_language_codes()
    if after == before:
        raise FeatureError(
            f"'{path.name}' was processed but no new language was registered.\n\n"
            "This usually means the .argosmodel file's internal structure was altered "
            "after downloading (for example, it was re-zipped, re-extracted-and-rezipped, "
            "or opened and re-saved by an archive tool). Delete this copy and download the "
            "original file fresh — do not re-compress or rename its contents."
        )
    return {"installed_languages": sorted(after)}


def argos_package_direct_urls(argos_from: str, argos_to: str) -> list[str]:
    """Return direct .argosmodel download URLs so a user behind a firewall can
    fetch the file with a browser and install it manually."""
    try:
        need("argostranslate", "argostranslate")
        import argostranslate.package as argos_package
        argos_package.update_package_index()
        for candidate in argos_package.get_available_packages():
            if candidate.from_code == argos_from and candidate.to_code == argos_to:
                links = [str(link) for link in (getattr(candidate, "links", None) or [])]
                return [link for link in links if link.startswith("http")]
    except Exception:
        pass
    # Stable naming convention used by the Argos package host
    return [f"https://argos-net.com/v1/translate-{argos_from}_{argos_to}-1_1.argosmodel"]


def argos_download_package(
    argos_from: str, argos_to: str, log: Optional[Callable[[str], None]] = None
) -> dict:
    """Download and install one language pack.
    Needs internet ONLY for this step; translation afterwards is fully offline."""
    need("argostranslate", "argostranslate")
    import argostranslate.package as argos_package

    if argos_from == argos_to:
        return {"installed": [], "note": "Source and target are the same."}
    if log:
        log(f"Checking the Argos package index for {argos_from} \u2192 {argos_to}\u2026")
    try:
        argos_package.update_package_index()
        available = argos_package.get_available_packages()
    except Exception as exc:
        raise FeatureError(
            "The Argos package index could not be reached.\n\n"
            f"Details: {str(exc)[:180]}\n\n"
            "This is usually a firewall or proxy. Download the pack manually instead:\n"
            "  1. Open https://www.argosopentech.com/argospm/index/ on any computer\n"
            f"  2. Download the {argos_from} \u2192 {argos_to} .argosmodel file\n"
            "  3. Copy it here and click 'Install downloaded pack'"
        ) from exc

    match = next(
        (c for c in available if c.from_code == argos_from and c.to_code == argos_to),
        None,
    )
    if match is None:
        raise FeatureError(
            f"Argos Translate does not publish a {argos_from} \u2192 {argos_to} package.\n\n"
            f"{ARGOS_UNSUPPORTED_NOTE}"
        )
    if log:
        log(f"Downloading {argos_from} \u2192 {argos_to} (this may take a minute)\u2026")
    try:
        downloaded = match.download()
        argos_package.install_from_path(str(downloaded))
    except Exception as exc:
        urls = argos_package_direct_urls(argos_from, argos_to)
        url_lines = "\n".join(f"  {u}" for u in urls)
        raise FeatureError(
            f"The download of {argos_from} \u2192 {argos_to} was blocked or failed.\n\n"
            f"Details: {str(exc)[:150]}\n\n"
            "This is almost always a corporate firewall or proxy blocking the model host.\n\n"
            "MANUAL INSTALL (works offline):\n"
            "  1. Open this link in a browser, on any computer with internet:\n"
            f"{url_lines}\n"
            "  2. Save the .argosmodel file.\n"
            "  3. Copy it to this computer (USB, network share, email).\n"
            "  4. Click 'Install downloaded pack' on this screen and select the file."
        ) from exc
    if log:
        log(f"Installed {argos_from} \u2192 {argos_to}.")
    return {"installed": [f"{argos_from}->{argos_to}"]}


def ensure_argos_pair_installed(
    source_app_code: str, target_app_code: str, log: Optional[Callable[[str], None]] = None
) -> None:
    """Downloads whichever of the two legs (source→en, en→target) are missing."""
    argos_source = ARGOS_LANGUAGES.get(source_app_code)
    argos_target = ARGOS_LANGUAGES.get(target_app_code)
    if argos_source is None or argos_target is None:
        raise FeatureError(ARGOS_UNSUPPORTED_NOTE)
    installed_pairs = _argos_installed_pairs()
    legs = []
    if argos_source != "en" and (argos_source, "en") not in installed_pairs:
        legs.append((argos_source, "en"))
    if argos_target != "en" and ("en", argos_target) not in installed_pairs:
        legs.append(("en", argos_target))
    for from_code, to_code in legs:
        argos_download_package(from_code, to_code, log=log)


def translate_text_offline(text: str, source_code: str, target_code: str) -> str:
    """Fully local translation via Argos Translate. No network calls are made here —
    the required language packages must already be installed (see argos_download_package)."""
    need("argostranslate", "argostranslate")
    import argostranslate.translate as argos_translate

    if source_code == target_code and source_code != "auto":
        return text
    argos_source = ARGOS_LANGUAGES.get(source_code)
    argos_target = ARGOS_LANGUAGES.get(target_code)
    if argos_source is None or argos_target is None:
        raise FeatureError(ARGOS_UNSUPPORTED_NOTE)
    if argos_source == "auto":
        raise FeatureError(
            "Auto-detect is handled before this step; a concrete source language is required."
        )

    installed_pairs = _argos_installed_pairs()

    def run_leg(chunk: str, from_code: str, to_code: str) -> str:
        if from_code == to_code:
            return chunk
        if (from_code, to_code) not in installed_pairs:
            raise FeatureError(
                f"The offline language pack for {from_code} → {to_code} is not installed. "
                "Use 'Download language pack' on the Translate screen (one-time, needs internet)."
            )
        return argos_translate.translate(chunk, from_code, to_code)

    translated: list[str] = []
    for chunk in _translation_chunks(text, limit=1800):
        if not chunk.strip():
            translated.append("")
            continue
        try:
            if argos_source == "en" or argos_target == "en":
                value = run_leg(chunk, argos_source, argos_target)
            else:
                # Argos ships X<->English pairs; pivot through English.
                via_english = run_leg(chunk, argos_source, "en")
                value = run_leg(via_english, "en", argos_target)
        except FeatureError:
            raise
        except Exception as exc:
            raise FeatureError(
                f"Offline translation failed for this passage.\n\nDetails: {str(exc)[:220]}"
            ) from exc
        translated.append(value or "")
    return "\n\n".join(translated).strip()


def translate_text(text: str, source_code: str, target_code: str, engine: str = "online") -> str:
    """Dispatches to the offline (Argos, local only) or online (Google/MyMemory) engine."""
    if engine == "offline":
        return translate_text_offline(text, source_code, target_code)
    return translate_text_online(text, source_code, target_code)


def _paragraphs_to_html(text: str) -> str:
    paragraphs = []
    for part in re.split(r"\n\s*\n", text.strip()):
        if part.strip():
            paragraphs.append(
                "<p>" + html_escape(part.strip()).replace("\n", "<br>") + "</p>"
            )
    return "".join(paragraphs) or "<p><i>(No text on this page)</i></p>"


def translate_pdf(
    input_path: str,
    output: str,
    source_code: str,
    target_code: str,
    use_ocr: bool,
    bilingual: bool,
    tesseract_path: Optional[str] = None,
    engine: str = "online",
) -> dict:
    """Create a clean, reflowed translated PDF with one output page per source page.
    engine: 'offline' uses Argos Translate (fully local, packs must be pre-installed);
    'online' uses Google Translate / MyMemory (requires internet)."""
    require_distinct_output(output, (input_path,))
    if target_code == "auto":
        raise FeatureError("Select a specific target language.")
    if engine == "offline":
        if not _module_available("argostranslate"):
            raise FeatureError(
                "The offline translation engine is not installed.\n\n"
                f"Install it once with:\n  {sys.executable} -m pip install argostranslate\n\n"
                "Then restart the application. Alternatively, switch the engine to Online."
            )
        ready, reason = argos_pair_ready(source_code, target_code)
        if not ready:
            raise FeatureError(
                f"Offline translation is not ready: {reason}\n\n"
                "TO FIX \u2014 either:\n"
                "  \u2022 Click 'Download language pack' on this screen (one-time, needs internet), or\n"
                "  \u2022 If your firewall blocks it, download the .argosmodel file manually from\n"
                "    https://www.argosopentech.com/argospm/index/ on any computer, copy it\n"
                "    across, then click 'Install downloaded pack'.\n\n"
                "Or switch the engine to Online."
            )
    pymupdf = get_pymupdf()
    source_pages = extract_pdf_text_pages(
        input_path, use_ocr, source_code, tesseract_path
    )
    if source_code == "auto":
        source_code = detect_language_code("\n".join(text for text in source_pages if text)[:5000])
        if engine == "offline" and not argos_is_language_supported(source_code):
            raise FeatureError(
                f"Detected source language '{source_code}' is not supported by the offline "
                f"engine.\n\n{ARGOS_UNSUPPORTED_NOTE}"
            )
    translated_pages = [
        translate_text(text, source_code, target_code, engine=engine) if text.strip() else ""
        for text in source_pages
    ]

    source_doc = pymupdf.open(input_path)
    output_doc = pymupdf.open()
    source_name = next((name for name, code in LANGUAGES.items() if code == source_code), source_code)
    target_name = next((name for name, code in LANGUAGES.items() if code == target_code), target_code)
    css = """
        * { font-family: sans-serif; }
        body { color: #12263F; font-size: 11pt; line-height: 1.4; }
        h2 { color: #22527E; font-size: 15pt; margin: 0 0 10pt 0; }
        p { margin: 0 0 7pt 0; text-align: justify; }
        .original { color: #5E7A96; background-color: #F2F7FC;
                    border: 1px solid #C3D8EC; padding: 8pt; }
        .label { color: #2C6BA0; font-size: 9pt; font-weight: bold; }
    """
    try:
        for index, translated in enumerate(translated_pages):
            source_page = source_doc[index]
            out_page = output_doc.new_page(width=source_page.rect.width, height=source_page.rect.height)
            header = (
                f"<h2>Translated page {index + 1}</h2>"
                f"<p class='label'>{html_escape(source_name)} → {html_escape(target_name)}</p>"
            )
            body = _paragraphs_to_html(translated)
            if bilingual:
                body += (
                    "<p class='label'>Original text</p><div class='original'>"
                    + _paragraphs_to_html(source_pages[index])
                    + "</div>"
                )
            rect = pymupdf.Rect(42, 38, out_page.rect.width - 42, out_page.rect.height - 38)
            if not hasattr(out_page, "insert_htmlbox"):
                raise FeatureError(
                    "PDF translation requires a current PyMuPDF release. Upgrade with: "
                    f"{sys.executable} -m pip install --upgrade pymupdf"
                )
            spare_height, scale = out_page.insert_htmlbox(
                rect, header + body, css=css, scale_low=0.45
            )
            if spare_height < 0:
                raise FeatureError(
                    f"Translated text on page {index + 1} is too long to fit. "
                    "Turn off bilingual output or split the source PDF into smaller sections."
                )
        output_doc.set_metadata({
            "title": f"Translated - {Path(input_path).name}",
            "subject": f"Translation from {source_name} to {target_name}",
            "creator": APP_NAME,
        })
        output_doc.save(output, garbage=4, deflate=True, clean=True)
    finally:
        output_doc.close()
        source_doc.close()
    return {
        "output": output,
        "pages": len(translated_pages),
        "source": source_name,
        "target": target_name,
        "bilingual": bilingual,
    }


def pdf_to_word(input_path: str, output: str, use_ocr: bool) -> dict:
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    if use_ocr or pdf_needs_ocr(input_path):
        need("docx", "python-docx")
        from docx import Document

        document = Document()
        for page_number, text in ocr_pdf_text(input_path):
            document.add_heading(f"Page {page_number}", level=2)
            for line in text.splitlines():
                if line.strip():
                    document.add_paragraph(line)
            if page_number:
                document.add_page_break()
        document.save(output)
        mode = "OCR"
    else:
        need("pdf2docx")
        from pdf2docx import Converter

        converter = Converter(input_path)
        try:
            converter.convert(output, start=0, end=None, multi_processing=False)
        finally:
            converter.close()
        mode = "layout"
    return {"output": output, "mode": mode}


def _clean_grid(grid: Sequence[Sequence[object]]) -> list[list[str]]:
    rows: list[list[str]] = []
    for row in grid:
        cleaned = [re.sub(r"\s*\n\s*", " ", str(value or "")).strip() for value in row]
        while cleaned and not cleaned[-1]:
            cleaned.pop()
        if any(cleaned):
            rows.append(cleaned)
    if not rows:
        return []
    max_columns = max(len(row) for row in rows)
    rows = [row + [""] * (max_columns - len(row)) for row in rows]
    keep_columns = [
        column for column in range(max_columns)
        if any(row[column].strip() for row in rows)
    ]
    return [[row[column] for column in keep_columns] for row in rows]


def _grid_score(grid: Sequence[Sequence[object]]) -> float:
    cleaned = _clean_grid(grid)
    if not cleaned:
        return 0.0
    columns = max(len(row) for row in cleaned)
    nonempty = sum(bool(cell) for row in cleaned for cell in row)
    density = nonempty / max(1, len(cleaned) * columns)
    column_bonus = 2.5 if columns >= 2 else 0.2
    return nonempty * density * column_bonus


def _page_has_ruling_lines(page) -> bool:
    """True when the page carries enough drawn lines to form a real table grid."""
    try:
        horizontal = sum(
            1 for edge in (page.edges or []) if edge.get("orientation") == "h"
        )
        vertical = sum(
            1 for edge in (page.edges or []) if edge.get("orientation") == "v"
        )
        return horizontal >= 3 and vertical >= 2
    except Exception:
        return False


def _best_pdfplumber_tables(page) -> list[list[list[str]]]:
    """Extract tables using ruled strategies only.

    The "text" strategy is deliberately excluded here: on borderless documents
    it infers column edges from character positions and routinely cuts through
    the middle of words and phrases (for example splitting "Income from House
    Property" across two cells). Borderless pages are handled instead by
    _words_to_grid, which clusters column positions across the whole page.
    """
    if not _page_has_ruling_lines(page):
        return []
    strategies = (
        {
            "vertical_strategy": "lines_strict", "horizontal_strategy": "lines_strict",
            "snap_tolerance": 3, "join_tolerance": 3, "intersection_tolerance": 5,
            "edge_min_length": 3,
        },
        {
            "vertical_strategy": "lines", "horizontal_strategy": "lines",
            "snap_tolerance": 4, "join_tolerance": 4, "intersection_tolerance": 6,
            "edge_min_length": 3,
        },
    )
    candidates: list[tuple[float, list[list[list[str]]]]] = []
    for settings in strategies:
        try:
            tables = [_clean_grid(table) for table in (page.extract_tables(settings) or [])]
        except Exception:
            continue
        tables = [table for table in tables if table]
        if tables:
            candidates.append((sum(_grid_score(table) for table in tables), tables))
    return max(candidates, key=lambda item: item[0])[1] if candidates else []


def _words_to_grid(words: Sequence[dict]) -> list[list[str]]:
    """Convert positioned words into a proper grid for borderless/OCR tables.

    Columns are derived once for the whole page by clustering the left edges of
    every word, then each word is assigned to the column it starts in. This is
    far more reliable than splitting each row on internal gaps, which wrongly
    breaks phrases such as "Income from House Property" into two cells.
    """
    usable = [w for w in words if str(w.get("text", "")).strip()]
    if not usable:
        return []

    # ── 1. Group words into visual rows ──
    heights = sorted(
        max(1.0, float(w.get("bottom", 0)) - float(w.get("top", 0))) for w in usable
    )
    median_height = heights[len(heights) // 2]
    y_tolerance = max(3.0, median_height * 0.6)

    ordered = sorted(
        usable, key=lambda w: (float(w.get("top", 0)), float(w.get("x0", 0)))
    )
    rows: list[list[dict]] = []
    centres: list[float] = []
    for word in ordered:
        centre = (float(word.get("top", 0)) + float(word.get("bottom", 0))) / 2
        if rows and abs(centre - centres[-1]) <= y_tolerance:
            rows[-1].append(word)
            count = len(rows[-1])
            centres[-1] = ((centres[-1] * (count - 1)) + centre) / count
        else:
            rows.append([word])
            centres.append(centre)
    for row in rows:
        row.sort(key=lambda w: float(w.get("x0", 0)))

    # ── 2. Find column boundaries for the whole page ──
    char_widths = sorted(
        (float(w.get("x1", 0)) - float(w.get("x0", 0))) / max(1, len(str(w.get("text", ""))))
        for w in usable if str(w.get("text", ""))
    )
    median_char = char_widths[len(char_widths) // 2] if char_widths else 4.0

    # A column starts where a word begins after a clear horizontal gap from the
    # previous word on the same row. Collect those starts across every row and
    # keep the ones that recur, which are the real column positions.
    candidates: list[float] = []
    gap_threshold = max(12.0, median_char * 3.2)
    for row in rows:
        if row:
            candidates.append(float(row[0].get("x0", 0)))
        for previous, current in zip(row, row[1:]):
            gap = float(current.get("x0", 0)) - float(previous.get("x1", 0))
            if gap >= gap_threshold:
                candidates.append(float(current.get("x0", 0)))

    if not candidates:
        return [[" ".join(str(w.get("text", "")) for w in row)] for row in rows]

    # Cluster nearby candidates into single column positions
    candidates.sort()
    cluster_width = max(10.0, median_char * 2.5)
    clusters: list[list[float]] = [[candidates[0]]]
    for value in candidates[1:]:
        if value - clusters[-1][-1] <= cluster_width:
            clusters[-1].append(value)
        else:
            clusters.append([value])

    # Keep columns that appear on enough rows to be genuine, always keeping the
    # first. This filters out one-off indents such as a centred heading.
    minimum_support = max(2, round(len(rows) * 0.25))
    boundaries: list[float] = []
    for index, cluster in enumerate(clusters):
        if index == 0 or len(cluster) >= minimum_support:
            boundaries.append(sum(cluster) / len(cluster))
    if not boundaries:
        boundaries = [min(candidates)]
    boundaries.sort()

    # ── 3. Assign each word to its column and join words within a cell ──
    def column_for(x_position: float) -> int:
        chosen = 0
        for index, boundary in enumerate(boundaries):
            if x_position >= boundary - cluster_width / 2:
                chosen = index
            else:
                break
        return chosen

    grid: list[list[str]] = []
    for row in rows:
        cells = [[] for _ in boundaries]
        for word in row:
            cells[column_for(float(word.get("x0", 0)))].append(
                str(word.get("text", "")).strip()
            )
        grid.append([" ".join(part for part in cell if part) for cell in cells])

    # Drop trailing columns that ended up completely empty
    while grid and all(not row[-1] for row in grid) and len(grid[0]) > 1:
        for row in grid:
            row.pop()
    return grid


def _ocr_pdf_word_pages(path: str, language: str = "eng") -> Iterable[tuple[int, list[dict]]]:
    pymupdf = get_pymupdf()
    need("pytesseract")
    need("PIL", "pillow")
    import pytesseract
    from PIL import Image

    configure_tesseract()

    doc = pymupdf.open(path)
    try:
        for page_number, page in enumerate(doc, start=1):
            pix = page.get_pixmap(dpi=250, alpha=False)
            image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
            try:
                data = pytesseract.image_to_data(
                    image, lang=language, config="--psm 6 -c preserve_interword_spaces=1",
                    output_type=pytesseract.Output.DICT,
                )
            except pytesseract.TesseractError as exc:
                lang_name = TESSERACT_LANG_NAMES.get(language, language)
                installed = get_available_tesseract_langs()
                installed_str = (
                    "Installed packs: " + ", ".join(installed)
                    if installed else "No language packs detected."
                )
                raise FeatureError(
                    f"Tesseract does not have the '{language}' ({lang_name}) language pack.\n\n"
                    f"{installed_str}\n\n"
                    "HOW TO FIX (choose one):\n"
                    "  1. Re-run the Tesseract installer and tick the missing language pack:\n"
                    "     https://github.com/UB-Mannheim/tesseract/wiki\n"
                    "     Expand 'Additional language data' during install.\n\n"
                    f"  2. Download only the missing file ({language}.traineddata):\n"
                    f"     https://github.com/tesseract-ocr/tessdata/raw/main/{language}.traineddata\n"
                    "     Save it to: C:\\Program Files\\Tesseract-OCR\\tessdata\\\n\n"
                    "  3. Change 'Source language' to 'Auto detect' or 'English' if your\n"
                    "     PDF has selectable text (OCR may not be needed at all)."
                ) from exc
            words = []
            for index, text in enumerate(data.get("text", [])):
                text = str(text).strip()
                try:
                    confidence = float(data["conf"][index])
                except (ValueError, TypeError, KeyError):
                    confidence = -1
                if not text or confidence < 10:
                    continue
                x, y = float(data["left"][index]), float(data["top"][index])
                width, height = float(data["width"][index]), float(data["height"][index])
                words.append({"text": text, "x0": x, "x1": x + width, "top": y, "bottom": y + height})
            yield page_number, words
    finally:
        doc.close()


def _write_grid(ws, grid: Sequence[Sequence[object]], start_row: int = 1) -> int:
    row_number = start_row
    for row in grid:
        for column, value in enumerate(row, start=1):
            ws.cell(row=row_number, column=column, value="" if value is None else str(value))
        row_number += 1
    return row_number


def _format_excel_sheet(ws, header_rows: Sequence[int]) -> None:
    from openpyxl.styles import Alignment, Border, Font, PatternFill, Side
    from openpyxl.utils import get_column_letter

    rust_fill = PatternFill("solid", fgColor="FF22527E")
    soft_fill = PatternFill("solid", fgColor="FF22527E")
    white_font = Font(color="FFFFFF", bold=True)
    thin = Side(style="thin", color="D8CEC5")
    border = Border(left=thin, right=thin, top=thin, bottom=thin)
    header_set = set(header_rows)
    for row in ws.iter_rows():
        for cell in row:
            if cell.value is None:
                continue
            cell.alignment = Alignment(vertical="top", wrap_text=True)
            cell.border = border
            if cell.row in header_set:
                cell.fill = rust_fill
                cell.font = white_font
            elif cell.row % 2 == 0:
                cell.fill = soft_fill
    for column in range(1, ws.max_column + 1):
        letter = get_column_letter(column)
        width = max(
            (len(str(ws.cell(row=row, column=column).value or "")) for row in range(1, ws.max_row + 1)),
            default=8,
        )
        ws.column_dimensions[letter].width = min(45, max(10, width + 2))
    if ws.max_row >= 2:
        ws.freeze_panes = "A2"
    ws.sheet_view.showGridLines = False


def pdf_to_excel(input_path: str, output: str, use_ocr: bool) -> dict:
    require_distinct_output(output, (input_path,))
    need("openpyxl")
    from openpyxl import Workbook

    workbook = Workbook()
    workbook.remove(workbook.active)
    check_size(input_path)
    ocr_mode = use_ocr or pdf_needs_ocr(input_path)
    total_tables = 0
    if ocr_mode:
        for page_number, words in _ocr_pdf_word_pages(input_path):
            ws = workbook.create_sheet(f"Page {page_number}"[:31])
            grid = _words_to_grid(words)
            if grid:
                _write_grid(ws, grid, 1)
                total_tables += 1
                _format_excel_sheet(ws, [1])
            else:
                ws.cell(1, 1, "No OCR text/table detected on this page")
    else:
        need("pdfplumber")
        import pdfplumber

        with pdfplumber.open(input_path) as pdf:
            for page_number, page in enumerate(pdf.pages, start=1):
                ws = workbook.create_sheet(f"Page {page_number}"[:31])
                row = 1
                header_rows: list[int] = []
                tables = _best_pdfplumber_tables(page)
                if tables:
                    for table in tables:
                        header_rows.append(row)
                        row = _write_grid(ws, table, row) + 1
                        total_tables += 1
                else:
                    grid = _words_to_grid(page.extract_words(
                        x_tolerance=2, y_tolerance=3, keep_blank_chars=False
                    ) or [])
                    if grid:
                        header_rows.append(1)
                        _write_grid(ws, grid, 1)
                    else:
                        ws.cell(1, 1, "No extractable text/table detected on this page")
                _format_excel_sheet(ws, header_rows)
    if not workbook.sheetnames:
        workbook.create_sheet("Empty")
    workbook.save(output)
    return {
        "output": output,
        "mode": "OCR positional table detection" if ocr_mode else "adaptive table detection",
        "tables": total_tables,
    }


def _office_or_libreoffice_to_pdf(input_path: str, output: str, kind: str) -> bool:
    """Use Microsoft Office on Windows, then LibreOffice. Return True on success."""
    if sys.platform.startswith("win"):
        try:
            import win32com.client  # type: ignore

            if kind == "word":
                app = win32com.client.DispatchEx("Word.Application")
                app.Visible = False
                document = app.Documents.Open(str(Path(input_path).resolve()), ReadOnly=True)
                try:
                    document.SaveAs(str(Path(output).resolve()), FileFormat=17)
                finally:
                    document.Close(False)
                    app.Quit()
            else:
                app = win32com.client.DispatchEx("Excel.Application")
                app.Visible = False
                app.DisplayAlerts = False
                workbook = app.Workbooks.Open(str(Path(input_path).resolve()), ReadOnly=True)
                try:
                    workbook.ExportAsFixedFormat(0, str(Path(output).resolve()))
                finally:
                    workbook.Close(False)
                    app.Quit()
            return Path(output).is_file() and Path(output).stat().st_size > 0
        except Exception:
            pass

    office = shutil.which("libreoffice") or shutil.which("soffice")
    if office:
        with tempfile.TemporaryDirectory(prefix="smart_pdf_office_") as work:
            result = subprocess.run(
                [office, "--headless", "--convert-to", "pdf", "--outdir", work, input_path],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=180,
                check=False,
            )
            generated = Path(work) / f"{Path(input_path).stem}.pdf"
            if result.returncode == 0 and generated.exists():
                shutil.copyfile(generated, output)
                return True
    return False


def word_to_pdf(input_path: str, output: str) -> dict:
    require_distinct_output(output, (input_path,))
    if _office_or_libreoffice_to_pdf(input_path, output, "word"):
        return {"output": output, "mode": "Office/LibreOffice"}
    need("docx", "python-docx")
    need("reportlab")
    from docx import Document
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.styles import getSampleStyleSheet
    from reportlab.lib.units import inch
    from reportlab.platypus import Paragraph, SimpleDocTemplate, Spacer, Table, TableStyle
    from xml.sax.saxutils import escape

    document = Document(input_path)
    pdf = SimpleDocTemplate(
        output, pagesize=A4, leftMargin=0.65 * inch, rightMargin=0.65 * inch,
        topMargin=0.65 * inch, bottomMargin=0.65 * inch,
    )
    styles = getSampleStyleSheet()
    story = []
    for child in document.element.body.iterchildren():
        tag = child.tag.split("}")[-1]
        if tag == "p":
            paragraph = next((p for p in document.paragraphs if p._element is child), None)
            if paragraph is None:
                continue
            text = paragraph.text.strip()
            if not text:
                story.append(Spacer(1, 6))
            else:
                style_name = paragraph.style.name if paragraph.style else "Normal"
                style = styles["Heading1"] if "Heading 1" in style_name else (
                    styles["Heading2"] if "Heading 2" in style_name else styles["BodyText"]
                )
                story.extend((Paragraph(escape(text), style), Spacer(1, 4)))
        elif tag == "tbl":
            table = next((t for t in document.tables if t._element is child), None)
            if table is not None:
                rows = [[cell.text for cell in row.cells] for row in table.rows]
                if rows:
                    item = Table(rows, repeatRows=1)
                    item.setStyle(TableStyle([
                        ("GRID", (0, 0), (-1, -1), 0.5, colors.grey),
                        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#E1EBF5")),
                        ("FONTSIZE", (0, 0), (-1, -1), 8),
                    ]))
                    story.extend((item, Spacer(1, 8)))
    if not story:
        story.append(Paragraph("(Empty document)", styles["BodyText"]))
    pdf.build(story)
    return {"output": output, "mode": "basic fallback"}


def excel_to_pdf(input_path: str, output: str) -> dict:
    require_distinct_output(output, (input_path,))
    if _office_or_libreoffice_to_pdf(input_path, output, "excel"):
        return {"output": output, "mode": "Office/LibreOffice"}
    need("openpyxl")
    need("reportlab")
    from openpyxl import load_workbook
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.lib.styles import getSampleStyleSheet
    from reportlab.lib.units import inch
    from reportlab.platypus import PageBreak, Paragraph, SimpleDocTemplate, Spacer, Table, TableStyle

    workbook = load_workbook(input_path, data_only=True)
    document = SimpleDocTemplate(
        output, pagesize=landscape(A4), leftMargin=0.35 * inch,
        rightMargin=0.35 * inch, topMargin=0.35 * inch, bottomMargin=0.35 * inch,
    )
    styles = getSampleStyleSheet()
    story = []
    for index, ws in enumerate(workbook.worksheets):
        story.extend((Paragraph(f"<b>{ws.title}</b>", styles["Heading2"]), Spacer(1, 5)))
        rows = [["" if value is None else str(value) for value in row]
                for row in ws.iter_rows(values_only=True)]
        if rows:
            table = Table(rows, repeatRows=1)
            table.setStyle(TableStyle([
                ("GRID", (0, 0), (-1, -1), 0.4, colors.grey),
                ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#22527E")),
                ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
                ("FONTSIZE", (0, 0), (-1, -1), 7),
                ("LEFTPADDING", (0, 0), (-1, -1), 3),
                ("RIGHTPADDING", (0, 0), (-1, -1), 3),
            ]))
            story.append(table)
        else:
            story.append(Paragraph("(Empty sheet)", styles["BodyText"]))
        if index < len(workbook.worksheets) - 1:
            story.append(PageBreak())
    document.build(story)
    return {"output": output, "mode": "basic fallback"}


def pdf_to_images(input_path: str, output_dir: str, image_format: str, dpi: int = 180) -> dict:
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected.")
    destination = Path(output_dir)
    destination.mkdir(parents=True, exist_ok=True)
    stem = safe_filename(Path(input_path).stem)
    outputs = []
    try:
        for number, page in enumerate(doc, start=1):
            pix = page.get_pixmap(dpi=dpi, alpha=image_format.lower() == "png")
            suffix = ".png" if image_format.lower() == "png" else ".jpg"
            target = unique_path(destination / f"{stem}_page_{number:03d}{suffix}")
            pix.save(str(target))
            outputs.append(str(target))
    finally:
        doc.close()
    return {"outputs": outputs, "count": len(outputs), "folder": str(destination)}


def images_to_pdf(inputs: Sequence[str], output: str) -> dict:
    require_distinct_output(output, inputs)
    need("PIL", "pillow")
    from PIL import Image

    if not inputs:
        raise FeatureError("Select at least one image.")
    images = []
    try:
        for filename in inputs:
            source = Image.open(filename)
            if source.mode == "RGBA":
                background = Image.new("RGB", source.size, "white")
                background.paste(source, mask=source.getchannel("A"))
                image = background
            else:
                image = source.convert("RGB")
            images.append(image)
        first, rest = images[0], images[1:]
        first.save(output, "PDF", save_all=True, append_images=rest, resolution=150.0)
    finally:
        for image in images:
            try:
                image.close()
            except Exception:
                pass
    return {"output": output, "pages": len(inputs)}


def compress_pdf(input_path: str, output: str, level: str) -> dict:
    require_distinct_output(output, (input_path,))
    pymupdf = get_pymupdf()
    original = Path(input_path).stat().st_size
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected.")
    processed: set[int] = set()
    try:
        if level in ("Medium", "High"):
            need("PIL", "pillow")
            from PIL import Image

            max_dimension = 1800 if level == "Medium" else 1200
            quality = 70 if level == "Medium" else 45
            for page in doc:
                for image_info in page.get_images(full=True):
                    xref = int(image_info[0])
                    if xref in processed:
                        continue
                    processed.add(xref)
                    try:
                        extracted = doc.extract_image(xref)
                        with Image.open(io.BytesIO(extracted["image"])) as image:
                            image = image.convert("RGB")
                            image.thumbnail((max_dimension, max_dimension), Image.Resampling.LANCZOS)
                            buffer = io.BytesIO()
                            image.save(buffer, "JPEG", quality=quality, optimize=True)
                            page.replace_image(xref, stream=buffer.getvalue())
                    except Exception:
                        continue
        save_options = dict(
            garbage=4,
            clean=True,
            deflate=True,
            deflate_images=True,
            deflate_fonts=True,
        )
        try:
            # Object streams improve compression in current PyMuPDF releases.
            doc.save(output, use_objstms=1, **save_options)
        except TypeError:
            # Keep compatibility with older supported PyMuPDF releases.
            doc.save(output, **save_options)
    finally:
        doc.close()
    compressed = Path(output).stat().st_size
    reduction = (1 - compressed / original) * 100 if original else 0.0
    return {
        "output": output,
        "original": original,
        "compressed": compressed,
        "reduction": reduction,
    }


def generate_test_certificate(
    output: str, common_name: str, organization: str, country: str,
    password: str, valid_days: int,
) -> dict:
    need("cryptography")
    from cryptography import x509
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.asymmetric import rsa
    from cryptography.hazmat.primitives.serialization import BestAvailableEncryption, pkcs12
    from cryptography.x509.oid import NameOID

    if not password:
        raise FeatureError("A password is required for the certificate.")
    key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    subject = issuer = x509.Name([
        x509.NameAttribute(NameOID.COUNTRY_NAME, (country or "IN")[:2].upper()),
        x509.NameAttribute(NameOID.ORGANIZATION_NAME, organization or "Self-Signed"),
        x509.NameAttribute(NameOID.COMMON_NAME, common_name or "Smart PDF Pro User"),
    ])
    now = datetime.now(timezone.utc)
    certificate = (
        x509.CertificateBuilder()
        .subject_name(subject)
        .issuer_name(issuer)
        .public_key(key.public_key())
        .serial_number(x509.random_serial_number())
        .not_valid_before(now - timedelta(minutes=5))
        .not_valid_after(now + timedelta(days=max(1, valid_days)))
        .add_extension(x509.BasicConstraints(ca=False, path_length=None), critical=True)
        .sign(key, hashes.SHA256())
    )
    data = pkcs12.serialize_key_and_certificates(
        name=common_name.encode("utf-8"), key=key, cert=certificate, cas=None,
        encryption_algorithm=BestAvailableEncryption(password.encode("utf-8")),
    )
    Path(output).write_bytes(data)
    return {"output": output}


def sign_pdf(
    input_path: str, certificate_path: str, password: str, output: str,
    signer_name: str, reason: str, location: str, visible: bool,
) -> dict:
    require_distinct_output(output, (input_path, certificate_path))
    need("pyhanko")
    from pyhanko import stamp
    from pyhanko.pdf_utils.incremental_writer import IncrementalPdfFileWriter
    from pyhanko.sign import PdfSignatureMetadata, signers
    from pyhanko.sign.fields import SigFieldSpec, SigSeedSubFilter, append_signature_field
    from pyhanko.sign.signers.pdf_signer import PdfSigner

    try:
        signer = signers.SimpleSigner.load_pkcs12(
            pfx_file=certificate_path,
            passphrase=password.encode("utf-8") if password else None,
        )
    except Exception as exc:
        raise FeatureError(
            "The PKCS#12 certificate could not be opened. Check that the file contains "
            "both the certificate and private key, and verify the password.\n\n"
            f"Details: {str(exc)[:220]}"
        ) from exc
    if signer is None:
        raise FeatureError("Invalid PKCS#12 certificate or password.")
    pypdf = need("pypdf")
    page_reader = pypdf.PdfReader(input_path)
    page_count = len(page_reader.pages)
    if not page_count:
        raise FeatureError("The selected PDF has no pages.")
    last_width = float(page_reader.pages[-1].mediabox.width)
    field_name = f"Signature-{uuid.uuid4().hex[:12]}"
    temporary = Path(output).with_name(f".{Path(output).name}.{uuid.uuid4().hex}.tmp")
    try:
        with open(input_path, "rb") as source, open(temporary, "wb") as target:
            writer = IncrementalPdfFileWriter(source)
            if visible:
                box = (last_width * 0.50, 32, last_width * 0.95, 122)
            else:
                box = None
            append_signature_field(
                writer,
                SigFieldSpec(sig_field_name=field_name, box=box, on_page=page_count - 1),
            )
            metadata = PdfSignatureMetadata(
                field_name=field_name,
                md_algorithm="sha256",
                subfilter=SigSeedSubFilter.PADES,
                name=signer_name or None,
                reason=reason or None,
                location=location or None,
            )
            stamp_style = stamp.TextStampStyle(
                stamp_text="Digitally signed by\n%(signer)s\n%(ts)s"
            ) if visible else None
            PdfSigner(metadata, signer=signer, stamp_style=stamp_style).sign_pdf(
                writer, output=target
            )
        if not temporary.exists() or temporary.stat().st_size <= Path(input_path).stat().st_size:
            raise FeatureError("Signing did not produce a valid incremental PDF output.")
        os.replace(temporary, output)
    except FeatureError:
        raise
    except Exception as exc:
        raise FeatureError(
            "Digital signing failed. Ensure pyHanko is current, the PDF is not damaged, "
            "and the certificate permits document signing.\n\n"
            f"Details: {str(exc)[:260]}"
        ) from exc
    finally:
        try:
            temporary.unlink(missing_ok=True)
        except Exception:
            pass
    return {"output": output, "field": field_name}


# ---------------------------------------------------------------------------
# v8 — multi-certificate signing, restriction removal, page-level editing
# ---------------------------------------------------------------------------

SIGNATURE_SCOPES = (
    "Last page only",
    "First page only",
    "All pages",
    "Selected pages",
)

SIGNATURE_POSITIONS = {
    "Bottom right": (0.62, 0.03, 0.96, 0.15),
    "Bottom left": (0.04, 0.03, 0.38, 0.15),
    "Bottom centre": (0.33, 0.03, 0.67, 0.15),
    "Top right": (0.62, 0.85, 0.96, 0.97),
    "Top left": (0.04, 0.85, 0.38, 0.97),
    "Top centre": (0.33, 0.85, 0.67, 0.97),
    "Middle right": (0.62, 0.44, 0.96, 0.56),
    "Custom": None,
}


def resolve_signature_pages(scope: str, pages_text: str, page_count: int) -> list[int]:
    """Turn a scope choice into a concrete list of zero-based page indices."""
    if page_count <= 0:
        raise FeatureError("The selected PDF has no pages.")
    if scope == "First page only":
        return [0]
    if scope == "All pages":
        return list(range(page_count))
    if scope == "Selected pages":
        if not pages_text.strip():
            raise FeatureError(
                "Enter the page numbers to sign, for example 1,3,5-7."
            )
        return parse_pages(pages_text, page_count)
    return [page_count - 1]  # Last page only (default)


def signature_box_for_page(
    position: str,
    page_width: float,
    page_height: float,
    custom_box: Optional[tuple] = None,
) -> tuple:
    """Return an absolute (x0, y0, x1, y1) stamp box in PDF points."""
    if position == "Custom":
        if not custom_box:
            raise FeatureError("Enter the custom signature co-ordinates.")
        return tuple(float(value) for value in custom_box)
    fractions = SIGNATURE_POSITIONS.get(position)
    if not fractions:
        fractions = SIGNATURE_POSITIONS["Bottom right"]
    left, bottom, right, top = fractions
    return (
        page_width * left,
        page_height * bottom,
        page_width * right,
        page_height * top,
    )


def render_signature_placements(input_path: str, certificates: Sequence[dict]) -> dict:
    """Fast, non-cryptographic preview: draw where each signature WOULD land.

    Used for real-time feedback while configuring signers — this never touches
    pyHanko or the certificate files, so it renders in milliseconds regardless
    of how many certificates are configured.
    """
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    page_count = doc.page_count
    palette = (
        (0.13, 0.32, 0.49), (0.68, 0.30, 0.05), (0.17, 0.46, 0.29),
        (0.45, 0.20, 0.55), (0.60, 0.13, 0.13),
    )
    try:
        for order, entry in enumerate(certificates):
            if not entry.get("visible", True):
                continue
            colour = palette[order % len(palette)]
            targets = resolve_signature_pages(
                entry.get("scope", "Last page only"),
                entry.get("pages_text", ""), page_count,
            )
            label = entry.get("signer_name") or Path(entry.get("path", "cert")).stem
            for page_index in targets:
                if page_index >= page_count:
                    continue
                page = doc[page_index]
                box = signature_box_for_page(
                    entry.get("position", "Bottom right"),
                    page.rect.width, page.rect.height,
                    entry.get("custom_box"),
                )
                rect = pymupdf.Rect(*box)
                page.draw_rect(rect, color=colour, width=1.6, dashes="[3 2] 0")
                page.draw_rect(rect, color=colour, fill=colour, fill_opacity=0.10, width=0)
                page.insert_textbox(
                    pymupdf.Rect(rect.x0, rect.y0 - 13, rect.x1 + 60, rect.y0),
                    f"[{order + 1}] {label}", fontsize=8, color=colour,
                    fontname="helv", align=0,
                )
        temporary = str(
            Path(tempfile.gettempdir()) / f"smartpdf_sig_preview_{uuid.uuid4().hex[:8]}.pdf"
        )
        doc.save(temporary, garbage=3, deflate=True)
    finally:
        doc.close()
    return {"output": temporary, "pages": page_count}


def sign_pdf_multi(
    input_path: str,
    output: str,
    certificates: Sequence[dict],
    log: Optional[Callable[[str], None]] = None,
) -> dict:
    """Apply one or more digital signatures to a PDF.

    Each entry in `certificates` is a dict:
        path, password, signer_name, reason, location,
        visible (bool), scope, pages_text, position, custom_box

    Signatures are applied sequentially as incremental updates, so every
    earlier signature stays cryptographically valid.
    """
    if not certificates:
        raise FeatureError("Add at least one digital signature certificate.")
    require_distinct_output(output, [input_path] + [c["path"] for c in certificates])
    need("pyhanko")
    from pyhanko import stamp
    from pyhanko.pdf_utils.incremental_writer import IncrementalPdfFileWriter
    from pyhanko.sign import PdfSignatureMetadata, signers
    from pyhanko.sign.fields import SigFieldSpec, SigSeedSubFilter, append_signature_field
    from pyhanko.sign.signers.pdf_signer import PdfSigner

    pypdf = need("pypdf")
    reader = pypdf.PdfReader(input_path)
    page_count = len(reader.pages)
    if not page_count:
        raise FeatureError("The selected PDF has no pages.")
    page_sizes = [
        (float(page.mediabox.width), float(page.mediabox.height))
        for page in reader.pages
    ]

    working = Path(input_path)
    temporary_files: list[Path] = []
    applied: list[dict] = []

    try:
        for order, entry in enumerate(certificates, start=1):
            certificate_path = entry["path"]
            password = entry.get("password") or ""
            if not Path(certificate_path).is_file():
                raise FeatureError(f"Certificate not found: {certificate_path}")
            try:
                signer = signers.SimpleSigner.load_pkcs12(
                    pfx_file=certificate_path,
                    passphrase=password.encode("utf-8") if password else None,
                )
            except Exception as exc:
                raise FeatureError(
                    f"Certificate {order} ({Path(certificate_path).name}) could not be "
                    "opened. Check that the .pfx/.p12 contains both the certificate and "
                    "the private key, and verify the password.\n\n"
                    f"Details: {str(exc)[:200]}"
                ) from exc
            if signer is None:
                raise FeatureError(
                    f"Certificate {order}: invalid PKCS#12 file or wrong password."
                )

            targets = resolve_signature_pages(
                entry.get("scope", "Last page only"),
                entry.get("pages_text", ""),
                page_count,
            )
            visible = bool(entry.get("visible", True))
            position = entry.get("position", "Bottom right")
            custom_box = entry.get("custom_box")

            for page_index in targets:
                if page_index >= page_count:
                    continue
                width, height = page_sizes[page_index]
                box = (
                    signature_box_for_page(position, width, height, custom_box)
                    if visible else None
                )
                field_name = f"Signature-{order}-P{page_index + 1}-{uuid.uuid4().hex[:8]}"
                destination = Path(output).with_name(
                    f".{Path(output).name}.{uuid.uuid4().hex}.tmp"
                )
                temporary_files.append(destination)
                if log:
                    log(
                        f"Signing page {page_index + 1} with "
                        f"{entry.get('signer_name') or Path(certificate_path).stem}…"
                    )
                try:
                    with open(working, "rb") as source, open(destination, "wb") as target:
                        writer = IncrementalPdfFileWriter(source)
                        append_signature_field(
                            writer,
                            SigFieldSpec(
                                sig_field_name=field_name,
                                box=box,
                                on_page=page_index,
                            ),
                        )
                        metadata = PdfSignatureMetadata(
                            field_name=field_name,
                            md_algorithm="sha256",
                            subfilter=SigSeedSubFilter.PADES,
                            name=entry.get("signer_name") or None,
                            reason=entry.get("reason") or None,
                            location=entry.get("location") or None,
                        )
                        stamp_style = (
                            stamp.TextStampStyle(
                                stamp_text="Digitally signed by\n%(signer)s\n%(ts)s"
                            )
                            if visible else None
                        )
                        PdfSigner(
                            metadata, signer=signer, stamp_style=stamp_style
                        ).sign_pdf(writer, output=target)
                except Exception as exc:
                    raise FeatureError(
                        f"Signing failed for certificate {order} on page "
                        f"{page_index + 1}.\n\n{str(exc)[:240]}"
                    ) from exc
                if not destination.exists() or destination.stat().st_size == 0:
                    raise FeatureError(
                        f"Signing produced an empty file on page {page_index + 1}."
                    )
                working = destination
                applied.append({
                    "certificate": Path(certificate_path).name,
                    "signer": entry.get("signer_name") or "",
                    "page": page_index + 1,
                    "field": field_name,
                    "visible": visible,
                })

        shutil.copyfile(working, output)
    finally:
        for path in temporary_files:
            if str(path) != str(working) or True:
                try:
                    if path.exists() and str(path) != str(output):
                        path.unlink()
                except Exception:
                    pass

    return {
        "output": output,
        "signatures": applied,
        "count": len(applied),
        "certificates": len(certificates),
    }


def pdf_restrictions(input_path: str) -> dict:
    """Report encryption state and which actions the PDF currently permits."""
    check_size(input_path)
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    try:
        info = {
            "encrypted": bool(doc.is_encrypted),
            "needs_password": bool(doc.needs_pass),
            "pages": doc.page_count if not doc.needs_pass else 0,
        }
        if not doc.needs_pass:
            permissions = int(doc.permissions)
            info["permissions"] = {
                "print": bool(permissions & int(pymupdf.PDF_PERM_PRINT)),
                "copy": bool(permissions & int(pymupdf.PDF_PERM_COPY)),
                "modify": bool(permissions & int(pymupdf.PDF_PERM_MODIFY)),
                "annotate": bool(permissions & int(pymupdf.PDF_PERM_ANNOTATE)),
                "form_fill": bool(permissions & int(pymupdf.PDF_PERM_FORM)),
                "assemble": bool(permissions & int(pymupdf.PDF_PERM_ASSEMBLE)),
                "extract_accessibility": bool(
                    permissions & int(pymupdf.PDF_PERM_ACCESSIBILITY)
                ),
            }
            info["restricted"] = not all(info["permissions"].values())
        return info
    finally:
        doc.close()


def unprotect_pdf(input_path: str, output: str, password: str = "") -> dict:
    """Remove owner restrictions (printing, copying, editing) from a PDF.

    Owner-password-only PDFs open without a password but block actions. This
    rewrites the document with no encryption so all actions are permitted.
    A user password, when set, must still be supplied.
    """
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    try:
        if doc.needs_pass:
            if not password:
                raise FeatureError(
                    "This PDF needs an open password before restrictions can be "
                    "removed.\n\nEnter the password, or use Unlock PDF if you only "
                    "want to remove the password."
                )
            if not doc.authenticate(password):
                raise FeatureError(
                    "The password is incorrect.\n\n"
                    "This tool removes restrictions from documents you are authorised "
                    "to use. It does not defeat unknown passwords."
                )
        before = int(doc.permissions)
        was_encrypted = bool(doc.is_encrypted)
        pages = doc.page_count
        # Saving with no encryption clears every restriction flag.
        doc.save(
            output,
            encryption=pymupdf.PDF_ENCRYPT_NONE,
            garbage=4,
            deflate=True,
            clean=True,
        )
    finally:
        doc.close()

    verify = pymupdf.open(output)
    try:
        after = int(verify.permissions)
        still_encrypted = bool(verify.is_encrypted)
    finally:
        verify.close()

    return {
        "output": output,
        "pages": pages,
        "was_encrypted": was_encrypted,
        "still_encrypted": still_encrypted,
        "permissions_before": before,
        "permissions_after": after,
        "unrestricted": not still_encrypted,
    }


def edit_page_transform(
    input_path: str,
    output: str,
    page_index: int,
    rotate_degrees: int = 0,
    crop: Optional[tuple] = None,
    crop_unit: str = "points",
) -> dict:
    """Rotate and/or crop one specific page, leaving all other pages untouched."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    try:
        if page_index < 0 or page_index >= doc.page_count:
            raise FeatureError(f"Page {page_index + 1} does not exist.")
        page = doc[page_index]
        actions: list[str] = []
        if crop:
            left, top, right, bottom = (float(value) for value in crop)
            rect = page.rect
            if crop_unit == "percent":
                left = rect.width * left / 100.0
                right = rect.width * right / 100.0
                top = rect.height * top / 100.0
                bottom = rect.height * bottom / 100.0
            new_rect = pymupdf.Rect(
                rect.x0 + left, rect.y0 + top, rect.x1 - right, rect.y1 - bottom
            )
            if new_rect.width < 10 or new_rect.height < 10:
                raise FeatureError(
                    "The crop margins leave less than 10 points of content. "
                    "Reduce the values."
                )
            page.set_cropbox(new_rect)
            actions.append("cropped")
        if rotate_degrees:
            page.set_rotation((page.rotation + int(rotate_degrees)) % 360)
            actions.append(f"rotated {int(rotate_degrees)}°")
        if not actions:
            raise FeatureError("Choose a rotation angle or enter crop margins.")
        doc.save(output, garbage=4, deflate=True, clean=True)
    finally:
        doc.close()
    return {"output": output, "page": page_index + 1, "actions": actions}


def render_page_thumbnail(input_path: str, page_index: int, dpi: int = 90):
    """Render one page to a PIL image, used for in-place edit previews."""
    pymupdf = get_pymupdf()
    need("PIL", "pillow")
    from PIL import Image

    doc = pymupdf.open(input_path)
    try:
        if doc.needs_pass:
            raise FeatureError("This PDF is password-protected. Unlock it first.")
        if page_index < 0 or page_index >= doc.page_count:
            raise FeatureError(f"Page {page_index + 1} does not exist.")
        pix = doc[page_index].get_pixmap(dpi=dpi, alpha=False)
        return Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
    finally:
        doc.close()


def verify_pdf_signatures(input_path: str) -> dict:
    need("pyhanko")
    from pyhanko.pdf_utils.reader import PdfFileReader
    from pyhanko.sign.validation import validate_pdf_signature
    from pyhanko_certvalidator import ValidationContext

    results = []
    with open(input_path, "rb") as source:
        reader = PdfFileReader(source)
        for embedded in reader.embedded_signatures:
            try:
                status = validate_pdf_signature(
                    embedded, ValidationContext(allow_fetching=False)
                )
                results.append({
                    "field": embedded.field_name,
                    "intact": bool(status.intact),
                    "valid": bool(status.valid),
                    "trusted": bool(status.trusted),
                    "summary": str(status.summary()),
                    "coverage": str(status.coverage).split(".")[-1],
                    "time": str(status.signer_reported_dt or "Not stated"),
                    "signer": (
                        status.signing_cert.subject.human_friendly
                        if status.signing_cert else "Unknown"
                    ),
                })
            except Exception as exc:
                results.append({"field": embedded.field_name, "error": str(exc)})
    return {"count": len(results), "signatures": results}


# ---------------------------------------------------------------------------
# Graphical interface
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# NEW FEATURES v3 — Crop, Protect, Unlock, Redact, Page Numbers, OCR,
# Compare, Repair, Forms, Edit, PDF/A, Markdown, PowerPoint, HTML, Scan
# ---------------------------------------------------------------------------


def crop_pdf(
    input_path: str,
    output: str,
    pages_text: str,
    left: float,
    top: float,
    right: float,
    bottom: float,
    unit: str = "points",
) -> dict:
    """Crop pages by trimming margins (points or percent of page size)."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    try:
        targets = parse_pages(pages_text, doc.page_count)
        for index in targets:
            page = doc[index]
            rect = page.rect
            if unit == "percent":
                dl = rect.width * left / 100.0
                dt = rect.height * top / 100.0
                dr = rect.width * right / 100.0
                db = rect.height * bottom / 100.0
            else:
                dl, dt, dr, db = left, top, right, bottom
            new_rect = pymupdf.Rect(
                rect.x0 + dl, rect.y0 + dt, rect.x1 - dr, rect.y1 - db
            )
            if new_rect.width < 10 or new_rect.height < 10:
                raise FeatureError(
                    f"Crop margins on page {index + 1} leave less than 10pt of content. "
                    "Reduce the margin values."
                )
            page.set_cropbox(new_rect)
        doc.save(output, garbage=4, deflate=True, clean=True)
    finally:
        doc.close()
    return {"output": output, "pages": len(targets)}


def protect_pdf(
    input_path: str,
    output: str,
    user_password: str,
    owner_password: str = "",
    allow_print: bool = True,
    allow_copy: bool = False,
    allow_modify: bool = False,
    allow_annotate: bool = False,
) -> dict:
    """Encrypt a PDF with AES-256 and set permission flags."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    if not user_password:
        raise FeatureError("Enter a password to protect the document.")
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is already password-protected. Unlock it first.")
    try:
        perm = int(pymupdf.PDF_PERM_ACCESSIBILITY)
        if allow_print:
            perm |= int(pymupdf.PDF_PERM_PRINT)
        if allow_copy:
            perm |= int(pymupdf.PDF_PERM_COPY)
        if allow_modify:
            perm |= int(pymupdf.PDF_PERM_MODIFY) | int(pymupdf.PDF_PERM_ASSEMBLE)
        if allow_annotate:
            perm |= int(pymupdf.PDF_PERM_ANNOTATE) | int(pymupdf.PDF_PERM_FORM)
        doc.save(
            output,
            encryption=pymupdf.PDF_ENCRYPT_AES_256,
            owner_pw=owner_password or user_password,
            user_pw=user_password,
            permissions=perm,
            garbage=4,
            deflate=True,
        )
    finally:
        doc.close()
    return {"output": output, "pages": 0, "encryption": "AES-256"}


def unlock_pdf(input_path: str, output: str, password: str) -> dict:
    """Remove password protection from a PDF (password must be known)."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    try:
        if doc.needs_pass:
            if not password:
                raise FeatureError("This PDF requires a password. Enter the password to unlock it.")
            if not doc.authenticate(password):
                raise FeatureError(
                    "The password is incorrect.\n\n"
                    "This tool removes protection from PDFs you have the password for. "
                    "It does not crack unknown passwords."
                )
        else:
            raise FeatureError("This PDF is not password-protected — no unlocking needed.")
        pages = doc.page_count
        doc.save(output, garbage=4, deflate=True, clean=True)
    finally:
        doc.close()
    return {"output": output, "pages": pages}


def find_text_in_pdf(input_path: str, search_terms: Sequence[str],
                     case_sensitive: bool = False, whole_word: bool = False) -> dict:
    """Search a PDF and return per-page hit counts and total occurrences."""
    check_size(input_path)
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    hits: dict[int, int] = {}
    total = 0
    try:
        flags = 0
        if not case_sensitive:
            flags |= pymupdf.TEXT_DEHYPHENATE
        for index in range(doc.page_count):
            page = doc[index]
            count = 0
            for term in search_terms:
                term = term.strip()
                if not term:
                    continue
                try:
                    areas = page.search_for(term, quads=False)
                except Exception:
                    areas = []
                count += len(areas)
            if count:
                hits[index + 1] = count
                total += count
    finally:
        doc.close()
    return {"hits": hits, "total": total, "terms": list(search_terms)}


def redact_pdf(
    input_path: str,
    output: str,
    search_terms: Sequence[str],
    pages_text: str = "",
    fill_black: bool = True,
    case_sensitive: bool = False,
) -> dict:
    """Permanently remove matching text (true redaction — content is destroyed)."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    terms = [t.strip() for t in search_terms if t.strip()]
    if not terms:
        raise FeatureError("Enter at least one word or phrase to redact.")
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    redacted = 0
    pages_touched: set[int] = set()
    try:
        targets = parse_pages(pages_text, doc.page_count) if pages_text.strip() else list(range(doc.page_count))
        fill = (0, 0, 0) if fill_black else (1, 1, 1)
        for index in targets:
            page = doc[index]
            for term in terms:
                try:
                    areas = page.search_for(term)
                except Exception:
                    continue
                for rect in areas:
                    page.add_redact_annot(rect, fill=fill)
                    redacted += 1
                    pages_touched.add(index + 1)
            if redacted:
                page.apply_redactions(images=pymupdf.PDF_REDACT_IMAGE_PIXELS)
        if redacted == 0:
            raise FeatureError(
                "No matches were found for the search terms.\n\n"
                "Check spelling, or note that scanned PDFs need OCR before text can be redacted."
            )
        doc.save(output, garbage=4, deflate=True, clean=True)
    finally:
        doc.close()
    return {"output": output, "redacted": redacted, "pages": sorted(pages_touched)}


def redact_pdf_areas(input_path: str, output: str,
                     areas: Sequence[tuple[int, float, float, float, float]]) -> dict:
    """Redact explicit rectangles: (page_index, x0, y0, x1, y1) in PDF points."""
    require_distinct_output(output, (input_path,))
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    try:
        touched: set[int] = set()
        for page_index, x0, y0, x1, y1 in areas:
            page = doc[page_index]
            page.add_redact_annot(pymupdf.Rect(x0, y0, x1, y1), fill=(0, 0, 0))
            touched.add(page_index)
        for page_index in touched:
            doc[page_index].apply_redactions(images=pymupdf.PDF_REDACT_IMAGE_PIXELS)
        doc.save(output, garbage=4, deflate=True, clean=True)
    finally:
        doc.close()
    return {"output": output, "redacted": len(areas)}


@dataclass
class RedactionRegion:
    """A pending redaction rectangle expressed in unscaled PDF points."""

    page_index: int
    rect: tuple[float, float, float, float]
    source: str = "manual"
    label: str = ""
    category: str = "Manual"


@dataclass
class SensitiveFinding:
    """A reviewable sensitive-data match found in a PDF."""

    finding_id: str
    page_index: int
    category: str
    value: str
    rect: tuple[float, float, float, float]
    selected: bool = True


SENSITIVE_PATTERNS: tuple[tuple[str, re.Pattern[str], Optional[Callable[[str], bool]]], ...] = (
    ("Email Address", re.compile(r"\b[A-Z0-9._%+\-]+@[A-Z0-9.\-]+\.[A-Z]{2,}\b", re.I), None),
    ("GSTIN", re.compile(r"\b\d{2}[A-Z]{5}\d{4}[A-Z][1-9A-Z]Z[0-9A-Z]\b", re.I), None),
    ("PAN", re.compile(r"\b[A-Z]{5}\d{4}[A-Z]\b", re.I), None),
    ("TAN", re.compile(r"\b[A-Z]{4}\d{5}[A-Z]\b", re.I), None),
    ("CIN", re.compile(r"\b[LU]\d{5}[A-Z]{2}\d{4}(?:PLC|PTC|FTC|NPL|OPC)\d{6}\b", re.I), None),
    ("LLPIN", re.compile(r"\b[A-Z]{3}-\d{4}\b", re.I), None),
    ("DIN", re.compile(r"\bDIN\s*[:#\-]?\s*(?P<value>\d{8})\b", re.I), None),
    ("FSSAI", re.compile(r"\bFSSAI(?:\s+(?:No|Number))?\s*[:#\-]?\s*(?P<value>\d{14})\b", re.I), None),
    ("Aadhaar", re.compile(r"\b[2-9]\d{3}[\s\-]?\d{4}[\s\-]?\d{4}\b"), None),
    ("Indian Passport", re.compile(r"\b[A-Z][1-9]\d{6}\b", re.I), None),
    ("Voter ID", re.compile(r"\b[A-Z]{3}\d{7}\b", re.I), None),
    ("Driving Licence", re.compile(r"\b[A-Z]{2}[\s\-]?\d{2}[\s\-]?(?:19|20)?\d{2}[\s\-]?\d{7}\b", re.I), None),
    ("IFSC", re.compile(r"\b[A-Z]{4}0[A-Z0-9]{6}\b", re.I), None),
    ("Bank Account", re.compile(r"\b(?:A/?C|Account)(?:\s+(?:No|Number))?\s*[:#\-]?\s*(?P<value>\d[\d\s\-]{7,20}\d)\b", re.I), None),
    ("Credit Card", re.compile(r"(?<!\d)(?:\d[ \-]?){13,19}(?!\d)"), None),
    ("US Social Security", re.compile(r"\b\d{3}-\d{2}-\d{4}\b"), None),
    ("UK National Insurance", re.compile(r"\b(?!BG|GB|NK|KN|TN|NT|ZZ)[A-CEGHJ-PR-TW-Z]{2}\s?\d{2}\s?\d{2}\s?\d{2}\s?[A-D]\b", re.I), None),
    ("Canadian SIN", re.compile(r"\b\d{3}[ \-]\d{3}[ \-]\d{3}\b"), None),
    ("Phone - India", re.compile(r"(?<!\d)(?:\+91[\s\-]?)?[6-9]\d{4}[\s\-]?\d{5}(?!\d)"), None),
    ("Phone - US", re.compile(r"(?<!\d)(?:\+?1[\s.\-]?)?\(?[2-9]\d{2}\)?[\s.\-]\d{3}[\s.\-]\d{4}(?!\d)"), None),
    ("Phone - UK", re.compile(r"(?<!\d)(?:\+44\s?7\d{3}|07\d{3})[\s\-]?\d{6}(?!\d)"), None),
    ("Medical Record No.", re.compile(r"\b(?:MRN|Medical\s+Record(?:\s+(?:No|Number))?)\s*[:#\-]?\s*(?P<value>[A-Z0-9\-/]{5,24})\b", re.I), None),
    ("Salary", re.compile(r"\b(?:Salary|CTC|Remuneration|Wages)\s*[:\-]?\s*(?P<value>(?:INR|Rs\.?|₹|USD|GBP|\$|£)\s*[\d,]+(?:\.\d{1,2})?)", re.I), None),
    ("Money Amount", re.compile(r"(?<!\w)(?:INR|Rs\.?|₹|USD|GBP|\$|£)\s*[\d,]+(?:\.\d{1,2})?", re.I), None),
    ("Website URL", re.compile(r"\b(?:https?://|www\.)[^\s<>()]+", re.I), None),
    ("IP Address", re.compile(r"\b(?:\d{1,3}\.){3}\d{1,3}\b"), None),
    ("Possible Birth Date", re.compile(r"\b(?:0?[1-9]|[12]\d|3[01])[\-/\.](?:0?[1-9]|1[0-2])[\-/\.](?:19|20)\d{2}\b"), None),
    ("Company Name", re.compile(r"\b[A-Z][A-Za-z&.'\-]*(?:\s+[A-Z][A-Za-z&.'\-]*){0,8}\s+(?:Private\s+Limited|Pvt\.?\s+Ltd\.?|Limited|Ltd\.?|LLP|LLC|Inc\.?|Corp\.?|Corporation|Enterprises|Industries)\b", re.I), None),
    ("Signature / Signatory", re.compile(r"\b(?:Signed\s+by|Signature\s+of|Authori[sz]ed\s+Signatory)\s*[:\-]?\s*(?P<value>[A-Z][A-Za-z.'\-]+(?:\s+[A-Z][A-Za-z.'\-]+){0,3})\b"), None),
    ("Person Name", re.compile(r"\b(?:Mr\.?|Mrs\.?|Ms\.?|Miss|Dr\.?|Shri|Smt\.?)\s+(?P<value>[A-Z][A-Za-z.'\-]+(?:\s+[A-Z][A-Za-z.'\-]+){1,3})\b"), None),
    ("Person Name", re.compile(r"\b(?:Name|Employee|Patient|Customer|Client)\s*[:\-]\s*(?P<value>[A-Z][A-Za-z.'\-]+(?:\s+[A-Z][A-Za-z.'\-]+){1,3})\b", re.I), None),
    ("Person Name", re.compile(r"\b[A-Z][a-z]{2,}(?:\s+[A-Z][a-z]{2,}){1,3}\b"), None),
)


NAME_FALSE_POSITIVES = {
    "Dear Sir", "Dear Madam", "Income Tax", "Goods Services", "Smart PDF",
    "Tax Invoice", "Bank Account", "Date Birth", "Date Joining", "New Delhi",
    "United States", "United Kingdom", "Private Limited", "Terms Conditions",
    "Authorized Signatory", "Authorised Signatory", "Page Number", "Total Amount",
}


def _valid_luhn(value: str) -> bool:
    digits = [int(ch) for ch in value if ch.isdigit()]
    if not 13 <= len(digits) <= 19 or len(set(digits)) == 1:
        return False
    total = 0
    parity = len(digits) % 2
    for index, digit in enumerate(digits):
        if index % 2 == parity:
            digit *= 2
            if digit > 9:
                digit -= 9
        total += digit
    return total % 10 == 0


def _valid_ip(value: str) -> bool:
    try:
        return all(0 <= int(part) <= 255 for part in value.split("."))
    except ValueError:
        return False


def _finding_rects(page, value: str) -> list[tuple[float, float, float, float]]:
    value = " ".join(value.split()).strip()
    if not value:
        return []
    try:
        return [tuple(float(n) for n in rect) for rect in page.search_for(value)]
    except Exception:
        return []


def find_pdf_occurrences(input_path: str, terms: Sequence[str],
                         category: str = "Search Match") -> list[SensitiveFinding]:
    """Find literal terms throughout a searchable PDF and return page rectangles."""
    check_size(input_path)
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    findings: list[SensitiveFinding] = []
    seen: set[tuple] = set()
    try:
        for page_index in range(doc.page_count):
            page = doc[page_index]
            for term in (item.strip() for item in terms):
                if not term:
                    continue
                for rect in _finding_rects(page, term):
                    key = (page_index, *(round(v, 2) for v in rect), term.casefold())
                    if key in seen:
                        continue
                    seen.add(key)
                    findings.append(SensitiveFinding(
                        uuid.uuid4().hex, page_index, category, term, rect, True
                    ))
    finally:
        doc.close()
    return findings


def analyze_sensitive_pdf(input_path: str,
                          progress: Optional[Callable[[int, int], None]] = None
                          ) -> list[SensitiveFinding]:
    """Pattern-based, local-only sensitive-data analysis for searchable PDFs."""
    check_size(input_path)
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    findings: list[SensitiveFinding] = []
    seen_rects: set[tuple] = set()

    def add(page_index: int, category: str, value: str,
            rect: tuple[float, float, float, float], selected: bool = True):
        key = (page_index, *(round(v, 1) for v in rect))
        if key in seen_rects:
            return
        seen_rects.add(key)
        findings.append(SensitiveFinding(
            uuid.uuid4().hex, page_index, category,
            " ".join(value.split())[:240], rect, selected
        ))

    try:
        total = doc.page_count
        for page_index in range(total):
            page = doc[page_index]
            text = page.get_text("text") or ""
            for category, pattern, validator in SENSITIVE_PATTERNS:
                for match in pattern.finditer(text):
                    value = match.groupdict().get("value") or match.group(0)
                    value = " ".join(value.split()).strip(" ,.;:")
                    if not value:
                        continue
                    if category == "Credit Card" and not _valid_luhn(value):
                        continue
                    if category == "IP Address" and not _valid_ip(value):
                        continue
                    if category == "Person Name" and value.title() in NAME_FALSE_POSITIVES:
                        continue
                    if validator and not validator(value):
                        continue
                    for rect in _finding_rects(page, value):
                        add(page_index, category, value, rect)

            # Address candidates: conservatively require a PIN and address wording.
            for block in page.get_text("blocks"):
                if len(block) < 5:
                    continue
                block_text = " ".join(str(block[4]).split())
                has_pin = re.search(r"\b[1-9]\d{5}\b", block_text)
                has_address_cue = re.search(
                    r"\b(?:address|road|street|lane|nagar|colony|building|floor|district|state|india)\b",
                    block_text, re.I
                )
                if has_pin and (has_address_cue or block_text.count(",") >= 2):
                    add(page_index, "Address with PIN", block_text,
                        tuple(float(n) for n in block[:4]))

            # A signature is often an image rather than text. Flag plausible small,
            # wide images for review only; do not preselect these heuristic matches.
            signature_context = bool(re.search(
                r"\b(?:signature|signed|signatory)\b", text, re.I
            ))
            try:
                image_blocks = page.get_text("dict").get("blocks", [])
            except Exception:
                image_blocks = []
            for block in image_blocks:
                if block.get("type") != 1:
                    continue
                x0, y0, x1, y1 = (float(n) for n in block.get("bbox", (0, 0, 0, 0)))
                width, height = x1 - x0, y1 - y0
                lower_page = y0 >= page.rect.height * 0.48
                if 35 <= width <= 360 and 12 <= height <= 160 and width / max(height, 1) >= 1.25:
                    if signature_context or lower_page:
                        add(page_index, "Possible Signature Image", "Image candidate",
                            (x0, y0, x1, y1), selected=False)

            # Ink/stamp annotations and signature-labelled form widgets are also
            # reviewable signature candidates. They remain unselected by default.
            try:
                annotations = list(page.annots() or [])
            except Exception:
                annotations = []
            for annotation in annotations:
                type_name = str(annotation.type[1]).casefold()
                if "ink" in type_name or "stamp" in type_name:
                    add(page_index, "Possible Signature Annotation", type_name.title(),
                        tuple(float(n) for n in annotation.rect), selected=False)
            try:
                widgets = list(page.widgets() or [])
            except Exception:
                widgets = []
            for widget in widgets:
                descriptor = " ".join(filter(None, (
                    str(getattr(widget, "field_name", "") or ""),
                    str(getattr(widget, "field_label", "") or ""),
                )))
                if re.search(r"\b(?:sign|signature|signatory)\b", descriptor, re.I):
                    add(page_index, "Possible Signature Field", descriptor or "Signature field",
                        tuple(float(n) for n in widget.rect), selected=False)

            if progress:
                progress(page_index + 1, total)
    finally:
        doc.close()
    return findings


PAGE_NUMBER_POSITIONS = {
    "Bottom centre": ("bottom", "centre"),
    "Bottom right": ("bottom", "right"),
    "Bottom left": ("bottom", "left"),
    "Top centre": ("top", "centre"),
    "Top right": ("top", "right"),
    "Top left": ("top", "left"),
}


def add_page_numbers(
    input_path: str,
    output: str,
    position: str = "Bottom centre",
    start_number: int = 1,
    first_page: int = 1,
    fmt: str = "{n}",
    font_size: int = 10,
    margin: float = 28.0,
) -> dict:
    """Stamp page numbers. fmt supports {n} (number) and {total}."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    try:
        vertical, horizontal = PAGE_NUMBER_POSITIONS.get(
            position, PAGE_NUMBER_POSITIONS["Bottom centre"]
        )
        total_numbered = doc.page_count - (first_page - 1)
        stamped = 0
        for index in range(first_page - 1, doc.page_count):
            page = doc[index]
            number = start_number + (index - (first_page - 1))
            label = fmt.replace("{n}", str(number)).replace("{total}", str(total_numbered))
            rect = page.rect
            text_width = len(label) * font_size * 0.5
            if horizontal == "centre":
                x = (rect.width - text_width) / 2
            elif horizontal == "right":
                x = rect.width - margin - text_width
            else:
                x = margin
            y = (rect.height - margin) if vertical == "bottom" else (margin + font_size)
            page.insert_text(
                pymupdf.Point(x, y), label,
                fontsize=font_size, fontname="helv", color=(0, 0, 0),
            )
            stamped += 1
        doc.save(output, garbage=4, deflate=True, clean=True)
    finally:
        doc.close()
    return {"output": output, "pages": stamped}


def ocr_pdf_searchable(
    input_path: str,
    output: str,
    language: str = "eng",
    dpi: int = 300,
    tesseract_path: Optional[str] = None,
) -> dict:
    """Create a searchable PDF: original page image + invisible OCR text layer."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    pymupdf = get_pymupdf()
    need("pytesseract")
    need("PIL", "pillow")
    import pytesseract
    from PIL import Image

    configure_tesseract(tesseract_path)
    source = pymupdf.open(input_path)
    if source.needs_pass:
        source.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    out = pymupdf.open()
    try:
        for page in source:
            pix = page.get_pixmap(dpi=dpi, alpha=False)
            image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
            try:
                pdf_bytes = pytesseract.image_to_pdf_or_hocr(
                    image, lang=language, extension="pdf"
                )
            except pytesseract.TesseractError as exc:
                lang_name = TESSERACT_LANG_NAMES.get(language, language)
                installed = get_available_tesseract_langs(tesseract_path)
                raise FeatureError(
                    f"Tesseract does not have the '{language}' ({lang_name}) language pack.\n\n"
                    f"Installed: {', '.join(installed) if installed else 'none detected'}\n\n"
                    f"Download: https://github.com/tesseract-ocr/tessdata/raw/main/{language}.traineddata\n"
                    "Save it to your Tesseract 'tessdata' folder."
                ) from exc
            piece = pymupdf.open("pdf", pdf_bytes)
            out.insert_pdf(piece)
            piece.close()
        out.set_metadata({
            "title": f"OCR - {Path(input_path).name}",
            "creator": APP_NAME,
        })
        out.save(output, garbage=4, deflate=True, clean=True)
        pages = out.page_count
    finally:
        out.close()
        source.close()
    return {"output": output, "pages": pages, "language": language}


def compare_pdfs(path_a: str, path_b: str) -> dict:
    """Compare two PDFs page by page and return a unified text diff summary."""
    import difflib

    check_size(path_a)
    check_size(path_b)
    pymupdf = get_pymupdf()

    def read_pages(path: str) -> list[str]:
        doc = pymupdf.open(path)
        if doc.needs_pass:
            doc.close()
            raise FeatureError(f"{Path(path).name} is password-protected. Unlock it first.")
        try:
            return [p.get_text("text", sort=True) for p in doc]
        finally:
            doc.close()

    pages_a, pages_b = read_pages(path_a), read_pages(path_b)
    max_pages = max(len(pages_a), len(pages_b))
    report_lines: list[str] = []
    changed_pages: list[int] = []
    added = removed = 0

    report_lines.append(f"FILE A : {Path(path_a).name}   ({len(pages_a)} pages)")
    report_lines.append(f"FILE B : {Path(path_b).name}   ({len(pages_b)} pages)")
    report_lines.append("=" * 74)

    if len(pages_a) != len(pages_b):
        report_lines.append(
            f"PAGE COUNT DIFFERS: A has {len(pages_a)}, B has {len(pages_b)}"
        )
        report_lines.append("")

    for index in range(max_pages):
        text_a = pages_a[index] if index < len(pages_a) else ""
        text_b = pages_b[index] if index < len(pages_b) else ""
        lines_a = [ln.rstrip() for ln in text_a.splitlines() if ln.strip()]
        lines_b = [ln.rstrip() for ln in text_b.splitlines() if ln.strip()]
        if lines_a == lines_b:
            continue
        changed_pages.append(index + 1)
        report_lines.append(f"--- PAGE {index + 1} ---")
        diff = difflib.unified_diff(lines_a, lines_b, lineterm="", n=1)
        for line in list(diff)[2:]:
            if line.startswith("+"):
                added += 1
                report_lines.append(f"  B+ {line[1:].strip()[:110]}")
            elif line.startswith("-"):
                removed += 1
                report_lines.append(f"  A- {line[1:].strip()[:110]}")
            elif line.startswith("@@"):
                report_lines.append("  ...")
        report_lines.append("")

    if not changed_pages:
        report_lines.append("NO TEXT DIFFERENCES FOUND — the documents match.")

    similarity = 0.0
    joined_a, joined_b = "\n".join(pages_a), "\n".join(pages_b)
    if joined_a or joined_b:
        similarity = difflib.SequenceMatcher(None, joined_a, joined_b).ratio() * 100

    return {
        "report": "\n".join(report_lines),
        "changed_pages": changed_pages,
        "added": added,
        "removed": removed,
        "similarity": round(similarity, 2),
        "pages_a": len(pages_a),
        "pages_b": len(pages_b),
    }


def repair_pdf(input_path: str, output: str) -> dict:
    """Rebuild a damaged/corrupt PDF by rewriting its object structure."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    pymupdf = get_pymupdf()
    notes: list[str] = []
    try:
        doc = pymupdf.open(input_path)
    except Exception as exc:
        raise FeatureError(
            f"The file could not be opened at all — it may not be a PDF or is severely damaged.\n\n"
            f"{str(exc)[:200]}"
        ) from exc
    try:
        if doc.needs_pass:
            doc.close()
            raise FeatureError("This PDF is password-protected. Unlock it first.")
        pages = doc.page_count
        if pages == 0:
            notes.append("Warning: the document reports 0 pages.")
        readable = 0
        for index in range(pages):
            try:
                doc[index].get_text("text")
                readable += 1
            except Exception:
                notes.append(f"Page {index + 1}: content stream could not be parsed.")
        # garbage=4 rebuilds the xref; clean=1 sanitises content streams
        doc.save(output, garbage=4, deflate=True, clean=True, incremental=False)
    finally:
        doc.close()
    size_before = Path(input_path).stat().st_size
    size_after = Path(output).stat().st_size
    return {
        "output": output,
        "pages": pages,
        "readable": readable,
        "notes": notes,
        "before": size_before,
        "after": size_after,
    }


def read_pdf_form_fields(input_path: str) -> dict:
    """List all interactive form fields and their current values."""
    check_size(input_path)
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    fields: list[dict] = []
    try:
        for page_index in range(doc.page_count):
            page = doc[page_index]
            for widget in page.widgets():
                fields.append({
                    "page": page_index + 1,
                    "name": widget.field_name or "(unnamed)",
                    "type": widget.field_type_string,
                    "value": widget.field_value,
                    "options": list(getattr(widget, "choice_values", None) or []),
                })
    finally:
        doc.close()
    return {"fields": fields, "count": len(fields)}


def fill_pdf_form(input_path: str, output: str, values: dict) -> dict:
    """Fill interactive form fields from a {field_name: value} mapping."""
    require_distinct_output(output, (input_path,))
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    filled = 0
    try:
        for page_index in range(doc.page_count):
            for widget in doc[page_index].widgets():
                name = widget.field_name
                if name in values:
                    new_value = values[name]
                    try:
                        if widget.field_type == pymupdf.PDF_WIDGET_TYPE_CHECKBOX:
                            widget.field_value = bool(new_value)
                        else:
                            widget.field_value = str(new_value)
                        widget.update()
                        filled += 1
                    except Exception:
                        continue
        doc.save(output, garbage=4, deflate=True)
    finally:
        doc.close()
    if filled == 0:
        raise FeatureError("No matching form fields were filled. Check the field names.")
    return {"output": output, "filled": filled}


def flatten_pdf_form(input_path: str, output: str) -> dict:
    """Flatten form fields so values become permanent page content."""
    require_distinct_output(output, (input_path,))
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    try:
        count = 0
        for page_index in range(doc.page_count):
            page = doc[page_index]
            for widget in list(page.widgets()):
                value = str(widget.field_value or "").strip()
                rect = widget.rect
                if value:
                    page.insert_textbox(
                        rect, value, fontsize=9, fontname="helv",
                        color=(0, 0, 0), align=0,
                    )
                page.delete_widget(widget)
                count += 1
        doc.save(output, garbage=4, deflate=True, clean=True)
    finally:
        doc.close()
    return {"output": output, "flattened": count}


def edit_pdf_add_text(
    input_path: str, output: str, page_index: int,
    text: str, x: float, y: float,
    font_size: int = 12, colour: tuple = (0, 0, 0),
) -> dict:
    """Add a text box at a given position on one page."""
    require_distinct_output(output, (input_path,))
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    try:
        if page_index >= doc.page_count:
            raise FeatureError(f"Page {page_index + 1} does not exist.")
        page = doc[page_index]
        page.insert_text(
            pymupdf.Point(x, y), text,
            fontsize=font_size, fontname="helv", color=colour,
        )
        doc.save(output, garbage=4, deflate=True)
    finally:
        doc.close()
    return {"output": output, "page": page_index + 1}


def edit_pdf_add_image(
    input_path: str, output: str, page_index: int,
    image_path: str, x: float, y: float, width: float, height: float,
) -> dict:
    """Place an image on one page at a given rectangle."""
    require_distinct_output(output, (input_path,))
    if not Path(image_path).is_file():
        raise FeatureError("Select a valid image file.")
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    try:
        page = doc[page_index]
        page.insert_image(
            pymupdf.Rect(x, y, x + width, y + height),
            filename=image_path, keep_proportion=True, overlay=True,
        )
        doc.save(output, garbage=4, deflate=True)
    finally:
        doc.close()
    return {"output": output, "page": page_index + 1}


def edit_pdf_add_shape(
    input_path: str, output: str, page_index: int, shape: str,
    x0: float, y0: float, x1: float, y1: float,
    colour: tuple = (0.9, 0.1, 0.1), width: float = 1.5, filled: bool = False,
) -> dict:
    """Draw a rectangle, ellipse or line on one page."""
    require_distinct_output(output, (input_path,))
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    try:
        page = doc[page_index]
        rect = pymupdf.Rect(x0, y0, x1, y1)
        fill = colour if filled else None
        if shape == "Rectangle":
            page.draw_rect(rect, color=colour, fill=fill, width=width)
        elif shape == "Ellipse":
            page.draw_oval(rect, color=colour, fill=fill, width=width)
        elif shape == "Line":
            page.draw_line(pymupdf.Point(x0, y0), pymupdf.Point(x1, y1),
                           color=colour, width=width)
        elif shape == "Highlight":
            page.draw_rect(rect, color=None, fill=(1, 1, 0), width=0, overlay=False)
        else:
            raise FeatureError(f"Unknown shape: {shape}")
        doc.save(output, garbage=4, deflate=True)
    finally:
        doc.close()
    return {"output": output, "page": page_index + 1, "shape": shape}


def pdf_to_markdown(input_path: str, output: str, use_ocr: bool = False,
                    tesseract_path: Optional[str] = None) -> dict:
    """Convert a PDF to Markdown, preserving headings, lists and tables where possible."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    # pymupdf4llm gives far better structure if installed
    try:
        import pymupdf4llm  # type: ignore
        md_text = pymupdf4llm.to_markdown(input_path)
        mode = "pymupdf4llm (structured)"
    except ImportError:
        pymupdf = get_pymupdf()
        doc = pymupdf.open(input_path)
        if doc.needs_pass:
            doc.close()
            raise FeatureError("This PDF is password-protected. Unlock it first.")
        parts: list[str] = []
        try:
            for index, page in enumerate(doc, start=1):
                parts.append(f"\n\n## Page {index}\n")
                blocks = page.get_text("dict").get("blocks", [])
                for block in blocks:
                    if block.get("type") != 0:
                        continue
                    for line in block.get("lines", []):
                        spans = line.get("spans", [])
                        if not spans:
                            continue
                        text = "".join(s.get("text", "") for s in spans).strip()
                        if not text:
                            continue
                        size = max((s.get("size", 10) for s in spans), default=10)
                        bold = any("bold" in str(s.get("font", "")).lower() for s in spans)
                        if size >= 16:
                            parts.append(f"\n### {text}\n")
                        elif size >= 13 or bold:
                            parts.append(f"\n**{text}**\n")
                        else:
                            parts.append(text)
                    parts.append("")
        finally:
            doc.close()
        md_text = "\n".join(parts)
        mode = "built-in heuristic"

    if not md_text.strip() and use_ocr:
        pages = extract_pdf_text_pages(input_path, True, "auto", tesseract_path)
        md_text = "\n\n".join(
            f"## Page {i}\n\n{t}" for i, t in enumerate(pages, start=1) if t.strip()
        )
        mode = "OCR"

    if not md_text.strip():
        raise FeatureError(
            "No text could be extracted. If this is a scanned PDF, tick 'Use OCR'."
        )

    header = f"# {Path(input_path).stem}\n\n> Converted from `{Path(input_path).name}` by {APP_NAME}\n"
    Path(output).write_text(header + md_text, encoding="utf-8")
    return {"output": output, "mode": mode, "characters": len(md_text)}


def pdf_to_powerpoint(input_path: str, output: str, dpi: int = 150) -> dict:
    """Convert each PDF page into a full-bleed PowerPoint slide image."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    need("pptx", "python-pptx")
    from pptx import Presentation
    from pptx.util import Emu

    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    presentation = Presentation()
    blank_layout = presentation.slide_layouts[6]
    try:
        first = doc[0].rect
        # Match slide size to PDF page aspect (points → EMU: 1pt = 12700 EMU)
        presentation.slide_width = Emu(int(first.width * 12700))
        presentation.slide_height = Emu(int(first.height * 12700))
        with tempfile.TemporaryDirectory(prefix="smartpdf_pptx_") as work:
            for index, page in enumerate(doc, start=1):
                pix = page.get_pixmap(dpi=dpi, alpha=False)
                image_path = str(Path(work) / f"page_{index:04d}.png")
                pix.save(image_path)
                slide = presentation.slides.add_slide(blank_layout)
                slide.shapes.add_picture(
                    image_path, 0, 0,
                    width=presentation.slide_width,
                    height=presentation.slide_height,
                )
            presentation.save(output)
        pages = doc.page_count
    finally:
        doc.close()
    return {"output": output, "pages": pages, "mode": f"page images @ {dpi} DPI"}


def powerpoint_to_pdf(input_path: str, output: str) -> dict:
    """Convert PPT/PPTX to PDF via MS Office (Windows) or LibreOffice."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    if sys.platform.startswith("win"):
        try:
            import win32com.client  # type: ignore
            app = win32com.client.DispatchEx("PowerPoint.Application")
            deck = app.Presentations.Open(
                str(Path(input_path).resolve()), WithWindow=False
            )
            try:
                deck.SaveAs(str(Path(output).resolve()), 32)  # 32 = ppSaveAsPDF
            finally:
                deck.Close()
                app.Quit()
            if Path(output).is_file() and Path(output).stat().st_size > 0:
                return {"output": output, "mode": "Microsoft PowerPoint"}
        except Exception:
            pass

    office = shutil.which("libreoffice") or shutil.which("soffice")
    if office:
        with tempfile.TemporaryDirectory(prefix="smartpdf_ppt_") as work:
            result = subprocess.run(
                [office, "--headless", "--convert-to", "pdf", "--outdir", work, input_path],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=240, check=False,
            )
            generated = Path(work) / f"{Path(input_path).stem}.pdf"
            if result.returncode == 0 and generated.exists():
                shutil.copyfile(generated, output)
                return {"output": output, "mode": "LibreOffice"}

    raise FeatureError(
        "PowerPoint → PDF needs Microsoft PowerPoint (Windows) or LibreOffice.\n\n"
        "Install LibreOffice from https://www.libreoffice.org/download/ and try again.\n"
        "On Windows, 'pip install pywin32' enables Microsoft Office automation."
    )


def html_to_pdf(source: str, output: str, is_url: bool = False,
                page_size: str = "A4", landscape: bool = False) -> dict:
    """Convert an HTML file, raw HTML string, or URL to PDF."""
    pymupdf = get_pymupdf()
    if is_url:
        try:
            import urllib.request
            request = urllib.request.Request(
                source, headers={"User-Agent": "Mozilla/5.0 SmartPDFPro"}
            )
            with urllib.request.urlopen(request, timeout=30) as response:
                html = response.read().decode("utf-8", errors="replace")
        except Exception as exc:
            raise FeatureError(
                f"Could not download the page:\n{source}\n\n{str(exc)[:200]}"
            ) from exc
    elif Path(source).is_file():
        require_distinct_output(output, (source,))
        html = Path(source).read_text(encoding="utf-8", errors="replace")
    else:
        html = source  # treat as raw HTML

    if not html.strip():
        raise FeatureError("The HTML content is empty.")

    sizes = {"A4": (595, 842), "Letter": (612, 792), "Legal": (612, 1008), "A3": (842, 1191)}
    width, height = sizes.get(page_size, sizes["A4"])
    if landscape:
        width, height = height, width

    if not hasattr(pymupdf, "Story"):
        raise FeatureError(
            "HTML → PDF needs a current PyMuPDF release.\n"
            f"Upgrade with: {sys.executable} -m pip install --upgrade pymupdf"
        )
    mediabox = pymupdf.Rect(0, 0, width, height)
    where = pymupdf.Rect(40, 40, width - 40, height - 40)
    pages = 0
    try:
        story = pymupdf.Story(html=html)
        writer = pymupdf.DocumentWriter(output)
        more = 1
        while more and pages < 500:
            device = writer.begin_page(mediabox)
            more, _ = story.place(where)
            story.draw(device)
            writer.end_page()
            pages += 1
        writer.close()
    except FeatureError:
        raise
    except Exception as exc:
        raise FeatureError(
            f"The HTML could not be rendered.\n\n{str(exc)[:200]}\n\n"
            "Complex CSS, JavaScript and external stylesheets are not supported. "
            "Simplify the HTML or print to PDF from your browser instead."
        ) from exc
    if pages == 0:
        raise FeatureError("The HTML produced no output pages.")
    return {"output": output, "pages": pages, "size": page_size}


def pdf_to_pdfa(input_path: str, output: str, level: str = "PDF/A-2b") -> dict:
    """Convert to PDF/A for long-term archival (uses Ghostscript when available)."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    ghostscript = (
        shutil.which("gswin64c") or shutil.which("gswin32c")
        or shutil.which("gs")
    )
    if ghostscript:
        level_map = {"PDF/A-1b": "1", "PDF/A-2b": "2", "PDF/A-3b": "3"}
        pdfa_level = level_map.get(level, "2")
        command = [
            ghostscript, "-dPDFA=" + pdfa_level, "-dBATCH", "-dNOPAUSE",
            "-dNOOUTERSAVE", "-sColorConversionStrategy=UseDeviceIndependentColor",
            "-sDEVICE=pdfwrite", "-dPDFACompatibilityPolicy=1",
            f"-sOutputFile={output}", input_path,
        ]
        try:
            result = subprocess.run(
                command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                timeout=300, check=False,
            )
            if result.returncode == 0 and Path(output).is_file():
                return {"output": output, "mode": f"Ghostscript {level}", "level": level}
        except Exception:
            pass

    # Fallback: PyMuPDF cannot certify PDF/A, but can produce a clean,
    # font-embedded, linearised PDF that is close to archival quality.
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    try:
        doc.set_metadata({
            "title": Path(input_path).stem,
            "creator": APP_NAME,
            "producer": f"{APP_NAME} archival export",
        })
        try:
            doc.save(output, garbage=4, deflate=True, clean=True, linear=True)
        except Exception:
            # Linearisation was removed in newer PyMuPDF releases
            doc.save(output, garbage=4, deflate=True, clean=True)
        pages = doc.page_count
    finally:
        doc.close()
    return {
        "output": output,
        "mode": "PyMuPDF clean export (not certified PDF/A)",
        "level": level,
        "pages": pages,
        "warning": (
            "Ghostscript was not found, so the output is a cleaned, linearised PDF "
            "rather than a certified PDF/A file.\n\n"
            "For true PDF/A compliance install Ghostscript:\n"
            "  Windows: https://ghostscript.com/releases/gsdnld.html\n"
            "  macOS:   brew install ghostscript\n"
            "  Linux:   sudo apt install ghostscript"
        ),
    }


def scan_to_pdf(
    inputs: Sequence[str],
    output: str,
    enhance: bool = True,
    grayscale: bool = False,
    deskew: bool = False,
    quality: int = 88,
) -> dict:
    """Turn photos/scans into a clean PDF with contrast and sharpening applied."""
    if not inputs:
        raise FeatureError("Select at least one scanned image.")
    require_distinct_output(output, inputs)
    need("PIL", "pillow")
    from PIL import Image, ImageEnhance, ImageFilter, ImageOps

    pages: list[Image.Image] = []
    try:
        for path in inputs:
            check_size(path)
            with Image.open(path) as raw:
                image = raw.convert("RGB")
                if deskew:
                    image = ImageOps.exif_transpose(image)
                if enhance:
                    image = ImageOps.autocontrast(image, cutoff=1)
                    image = ImageEnhance.Sharpness(image).enhance(1.6)
                    image = ImageEnhance.Contrast(image).enhance(1.25)
                    image = image.filter(ImageFilter.UnsharpMask(radius=1.4, percent=115))
                if grayscale:
                    image = image.convert("L").convert("RGB")
                pages.append(image.copy())
        if not pages:
            raise FeatureError("None of the selected images could be read.")
        pages[0].save(
            output, "PDF", save_all=True, append_images=pages[1:],
            resolution=200.0, quality=quality,
        )
    finally:
        for image in pages:
            try:
                image.close()
            except Exception:
                pass
    return {"output": output, "pages": len(inputs), "enhanced": enhance}


def rotate_pdf_pages(input_path: str, output: str, pages_text: str, degrees: int) -> dict:
    """Rotate selected pages by a fixed angle without changing page order."""
    require_distinct_output(output, (input_path,))
    check_size(input_path)
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    try:
        targets = parse_pages(pages_text, doc.page_count)
        for index in targets:
            page = doc[index]
            page.set_rotation((page.rotation + degrees) % 360)
        doc.save(output, garbage=4, deflate=True, clean=True)
    finally:
        doc.close()
    return {"output": output, "pages": len(targets), "degrees": degrees}


def insert_pages_into_pdf(
    base_path: str, insert_path: str, output: str, after_page: int
) -> dict:
    """Insert all pages of one PDF into another after a given page (0 = at start)."""
    require_distinct_output(output, (base_path, insert_path))
    pymupdf = get_pymupdf()
    base = pymupdf.open(base_path)
    extra = pymupdf.open(insert_path)
    try:
        if base.needs_pass or extra.needs_pass:
            raise FeatureError("One of the PDFs is password-protected. Unlock it first.")
        if after_page < 0 or after_page > base.page_count:
            raise FeatureError(f"Insert position must be between 0 and {base.page_count}.")
        base.insert_pdf(extra, start_at=after_page)
        base.save(output, garbage=4, deflate=True, clean=True)
        total = base.page_count
    finally:
        base.close()
        extra.close()
    return {"output": output, "pages": total, "inserted": after_page}


def extract_pdf_pages(input_path: str, output: str, pages_text: str) -> dict:
    """Extract selected pages into a new single PDF."""
    require_distinct_output(output, (input_path,))
    pymupdf = get_pymupdf()
    doc = pymupdf.open(input_path)
    if doc.needs_pass:
        doc.close()
        raise FeatureError("This PDF is password-protected. Unlock it first.")
    try:
        targets = parse_pages(pages_text, doc.page_count)
        out = pymupdf.open()
        for index in targets:
            out.insert_pdf(doc, from_page=index, to_page=index)
        out.save(output, garbage=4, deflate=True, clean=True)
        out.close()
    finally:
        doc.close()
    return {"output": output, "pages": len(targets)}


class ToolTip:
    def __init__(self, widget: tk.Widget, text: str):
        self.widget, self.text, self.window = widget, text, None
        widget.bind("<Enter>", self.show, add="+")
        widget.bind("<Leave>", self.hide, add="+")

    def show(self, _event=None):
        if self.window or not self.text:
            return
        x = self.widget.winfo_rootx() + 20
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 4
        self.window = win = tk.Toplevel(self.widget)
        win.wm_overrideredirect(True)
        win.wm_geometry(f"+{x}+{y}")
        tk.Label(
            win, text=self.text, bg=COLORS["ink"], fg="white", padx=8, pady=5,
            font=("Segoe UI", 9), wraplength=320, justify="left",
        ).pack()

    def hide(self, _event=None):
        if self.window:
            self.window.destroy()
            self.window = None


class PreviewPanel(ttk.Frame):
    def __init__(self, master):
        super().__init__(master, style="Panel.TFrame", padding=12)
        self.path: Optional[str] = None
        self.page_index = 0
        self.page_count = 0
        self.photo = None

        ttk.Label(self, text="DOCUMENT PREVIEW", style="Eyebrow.TLabel").pack(anchor="w")
        self.name_var = tk.StringVar(value="Select a PDF to preview")
        ttk.Label(self, textvariable=self.name_var, style="PanelTitle.TLabel", wraplength=380).pack(
            anchor="w", pady=(5, 10)
        )
        # Canvas with its own independent vertical + horizontal scrollbars,
        # so a zoomed page can be panned without affecting the form column.
        canvas_wrap = ttk.Frame(self, style="Panel.TFrame")
        canvas_wrap.pack(fill="both", expand=True)
        self.canvas = tk.Canvas(
            canvas_wrap, bg=COLORS["blue_050"], highlightthickness=1,
            highlightbackground=COLORS["line"], width=420, height=400
        )
        self.v_scroll = ttk.Scrollbar(
            canvas_wrap, orient="vertical", command=self.canvas.yview
        )
        self.h_scroll = ttk.Scrollbar(
            canvas_wrap, orient="horizontal", command=self.canvas.xview
        )
        self.canvas.configure(
            yscrollcommand=self.v_scroll.set, xscrollcommand=self.h_scroll.set
        )
        self.v_scroll.grid(row=0, column=1, sticky="ns")
        self.h_scroll.grid(row=1, column=0, sticky="ew")
        self.canvas.grid(row=0, column=0, sticky="nsew")
        canvas_wrap.rowconfigure(0, weight=1)
        canvas_wrap.columnconfigure(0, weight=1)

        self.zoom = 1.0

        def _preview_wheel(event):
            step = -1 if getattr(event, "num", 0) == 5 or getattr(event, "delta", 0) < 0 else 1
            if event.state & 0x0004:          # Ctrl held → zoom
                self.set_zoom(self.zoom * (1.1 if step > 0 else 0.9))
            else:                              # otherwise scroll the page image
                self.canvas.yview_scroll(-step, "units")
            return "break"

        for sequence in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.canvas.bind(sequence, _preview_wheel)
        # Click-drag to pan
        self.canvas.bind("<ButtonPress-1>", lambda e: self.canvas.scan_mark(e.x, e.y))
        self.canvas.bind("<B1-Motion>", lambda e: self.canvas.scan_dragto(e.x, e.y, gain=1))

        # Before / After switch — appears only once a result preview exists
        self.compare_bar = ttk.Frame(self, style="Panel.TFrame")
        self.compare_mode = tk.StringVar(value="after")
        self._original_path: Optional[str] = None
        self._result_path: Optional[str] = None
        ttk.Label(self.compare_bar, text="Showing:", style="Help.TLabel").pack(
            side="left", padx=(0, 8)
        )
        for label, value in (("Before", "before"), ("After", "after")):
            ttk.Radiobutton(
                self.compare_bar, text=label, value=value,
                variable=self.compare_mode, command=self._compare_changed,
            ).pack(side="left", padx=(0, 10))
        self.compare_note = ttk.Label(
            self.compare_bar, text="Preview only — not saved", style="Help.TLabel"
        )
        self.compare_note.pack(side="right")

        nav = ttk.Frame(self, style="Panel.TFrame")
        nav.pack(fill="x", pady=(10, 0))
        self.prev_btn = ttk.Button(nav, text="‹ Previous", command=self.previous, style="Quiet.TButton")
        self.prev_btn.pack(side="left")
        self.page_var = tk.StringVar(value="—")
        ttk.Label(nav, textvariable=self.page_var, style="Panel.TLabel").pack(side="left", expand=True)
        self.next_btn = ttk.Button(nav, text="Next ›", command=self.next, style="Quiet.TButton")
        self.next_btn.pack(side="right")

        zoom_row = ttk.Frame(self, style="Panel.TFrame")
        zoom_row.pack(fill="x", pady=(6, 0))
        ttk.Button(zoom_row, text="\u2212", width=3, style="Quiet.TButton",
                   command=lambda: self.set_zoom(self.zoom * 0.85)).pack(side="left")
        ttk.Button(zoom_row, text="+", width=3, style="Quiet.TButton",
                   command=lambda: self.set_zoom(self.zoom * 1.18)).pack(side="left", padx=(3, 0))
        ttk.Button(zoom_row, text="Fit", width=4, style="Quiet.TButton",
                   command=lambda: self.set_zoom(1.0)).pack(side="left", padx=(3, 0))
        self.zoom_var = tk.StringVar(value="100%")
        ttk.Label(zoom_row, textvariable=self.zoom_var, style="Help.TLabel").pack(
            side="left", padx=(8, 0)
        )
        ttk.Label(zoom_row, text="Ctrl+wheel zooms",
                  style="Help.TLabel").pack(side="right")
        self.canvas.bind("<Configure>", lambda _e: self.render())
        # Re-render when the pane is mapped, so a preview loaded while the page
        # was hidden is redrawn at the correct size as soon as it is shown.
        self.bind("<Map>", lambda _e: self.after(60, self.render))
        self.canvas.bind("<Map>", lambda _e: self.after(60, self.render))

    def show_comparison(self, original: str, result: str, page: int = 0):
        """Display a proposed result with a Before/After switch."""
        self._original_path = original
        self._result_path = result
        self.compare_mode.set("after")
        if not self.compare_bar.winfo_ismapped():
            self.compare_bar.pack(fill="x", pady=(8, 0), before=self.canvas.master)
        self.compare_note.configure(
            text="Preview only — not saved", foreground=COLORS["blue_700"]
        )
        self.load(result, page=page)

    def clear_comparison(self):
        """Leave comparison mode (called once a real file has been saved)."""
        self._original_path = None
        self._result_path = None
        if self.compare_bar.winfo_ismapped():
            self.compare_bar.pack_forget()

    def _compare_changed(self):
        page = self.page_index
        target = (
            self._original_path if self.compare_mode.get() == "before"
            else self._result_path
        )
        if target and Path(target).is_file():
            self.load(target, page=page)

    def set_zoom(self, value: float):
        self.zoom = max(0.25, min(6.0, float(value)))
        if hasattr(self, "zoom_var"):
            self.zoom_var.set(f"{round(self.zoom * 100)}%")
        self.render()

    def clear(self, text: str = "Select a PDF to preview"):
        self.path, self.page_count, self.page_index, self.photo = None, 0, 0, None
        self.name_var.set(text)
        self.page_var.set("—")
        self.canvas.delete("all")
        self.canvas.create_text(
            max(20, self.canvas.winfo_width() // 2), max(20, self.canvas.winfo_height() // 2),
            text="PDF preview appears here", fill=COLORS["muted"], font=("Segoe UI", 11)
        )

    def load(self, path: str, page: int = 0):
        if not path or Path(path).suffix.lower() != ".pdf" or not Path(path).is_file():
            self.clear("Preview supports PDF files")
            return
        try:
            pymupdf = get_pymupdf()
            doc = pymupdf.open(path)
            if doc.needs_pass:
                raise FeatureError("Password-protected PDF")
            count = doc.page_count
            doc.close()
            self.path = path
            self.page_count = count
            self.page_index = max(0, min(page, count - 1))
            self.name_var.set(Path(path).name)
            self.render()
        except Exception as exc:
            self.clear(f"Preview unavailable: {exc}")

    def render(self):
        if not self.path or not self.page_count:
            return
        try:
            pymupdf = get_pymupdf()
            need("PIL", "pillow")
            from PIL import Image, ImageTk

            doc = pymupdf.open(self.path)
            page = doc[self.page_index]
            view_w = self.canvas.winfo_width()
            view_h = self.canvas.winfo_height()
            if view_w < 80 or view_h < 80:
                # The pane has not been laid out yet (page still hidden, or the
                # very first render). Retry shortly instead of drawing a stamp-
                # sized page that never corrects itself.
                if getattr(self, "_render_retries", 0) < 12:
                    self._render_retries = getattr(self, "_render_retries", 0) + 1
                    self.after(90, self.render)
                    return
                view_w, view_h = max(view_w, 380), max(view_h, 420)
            self._render_retries = 0
            fit = min((view_w - 28) / page.rect.width, (view_h - 28) / page.rect.height)
            scale = max(0.05, fit * getattr(self, "zoom", 1.0))
            pix = page.get_pixmap(matrix=pymupdf.Matrix(scale, scale), alpha=False)
            image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
            doc.close()
            self.photo = ImageTk.PhotoImage(image)
            self.canvas.delete("all")
            # Centre the page when it is smaller than the viewport, otherwise
            # anchor it so the scrollbars can pan across the whole image.
            canvas_w = max(view_w, image.width + 28)
            canvas_h = max(view_h, image.height + 28)
            x, y = canvas_w // 2, canvas_h // 2
            self.canvas.create_rectangle(
                x - image.width // 2 - 3, y - image.height // 2 - 3,
                x + image.width // 2 + 3, y + image.height // 2 + 3,
                fill=COLORS["blue_200"], outline=""
            )
            self.canvas.create_image(x, y, image=self.photo)
            self.canvas.configure(scrollregion=(0, 0, canvas_w, canvas_h))
            self.page_var.set(f"Page {self.page_index + 1} of {self.page_count}")
            self.prev_btn.state(["disabled"] if self.page_index == 0 else ["!disabled"])
            self.next_btn.state(["disabled"] if self.page_index >= self.page_count - 1 else ["!disabled"])
        except Exception as exc:
            self.clear(f"Preview unavailable: {exc}")

    def previous(self):
        if self.page_index > 0:
            self.page_index -= 1
            self.render()

    def next(self):
        if self.page_index + 1 < self.page_count:
            self.page_index += 1
            self.render()


class BasePage(ttk.Frame):
    title = "Tool"
    description = ""

    def __init__(self, master, app: "SmartPDFPro"):
        super().__init__(master, style="App.TFrame", padding=(24, 20))
        self.app = app
        header = tk.Frame(self, bg=COLORS["white"], padx=0, pady=0)
        header.pack(fill="x", pady=(0, 16))
        inner = tk.Frame(header, bg=COLORS["white"], padx=20, pady=15)
        inner.pack(fill="x")
        tk.Frame(inner, bg=COLORS["blue_700"], width=3).pack(side="left", fill="y", padx=(0, 15))
        heading = tk.Frame(inner, bg=COLORS["white"])
        heading.pack(side="left", fill="both", expand=True)
        tk.Label(
            heading, text=self.title, bg=COLORS["white"], fg=COLORS["blue_900"],
            font=("Segoe UI Semilight", 18), anchor="w",
        ).pack(anchor="w")
        tk.Label(
            heading, text=self.description, bg=COLORS["white"], fg=COLORS["muted"],
            font=("Segoe UI", 9), anchor="w", justify="left", wraplength=760,
        ).pack(anchor="w", pady=(3, 0))
        tk.Frame(header, bg=COLORS["blue_200"], height=1).pack(fill="x")

        body = ttk.Panedwindow(self, orient="horizontal")
        body.pack(fill="both", expand=True)
        self._paned = body

        def _set_initial_sash(_event=None):
            try:
                total = body.winfo_width()
                if total > 400:
                    # Give the form ~62% of the width so labels are never clipped
                    body.sashpos(0, int(total * 0.62))
                    body.unbind("<Map>")
                    if hasattr(self, "_rewrap_controls"):
                        self.after(60, self._rewrap_controls)
            except Exception:
                pass

        body.bind("<Map>", _set_initial_sash)

        controls_outer = ttk.Frame(body, style="Panel.TFrame")
        controls_canvas = tk.Canvas(
            controls_outer, bg=COLORS["panel"], highlightthickness=0
        )
        controls_scroll = ttk.Scrollbar(
            controls_outer, orient="vertical", command=controls_canvas.yview
        )
        self.controls = ttk.Frame(controls_canvas, style="Panel.TFrame", padding=18)
        controls_window = controls_canvas.create_window(
            (0, 0), window=self.controls, anchor="nw"
        )

        def _sync_controls(_event=None):
            controls_canvas.configure(scrollregion=controls_canvas.bbox("all"))
            controls_canvas.itemconfigure(
                controls_window, width=controls_canvas.winfo_width()
            )

        def _rewrap(_event=None):
            """Re-wrap every wrapping label to the pane's real width so nothing
            is ever clipped when the window or sash is resized."""
            width = controls_canvas.winfo_width()
            if width < 60:
                return
            target = max(180, width - 92)
            for widget in self.controls.winfo_children():
                _rewrap_tree(widget, target)

        def _rewrap_tree(widget, target):
            try:
                if isinstance(widget, (tk.Label, ttk.Label)):
                    if int(str(widget.cget("wraplength")) or 0):
                        widget.configure(wraplength=target)
            except Exception:
                pass
            for child in widget.winfo_children():
                _rewrap_tree(child, target)

        self.controls.bind("<Configure>", _sync_controls)
        controls_canvas.bind("<Configure>", lambda e: (_sync_controls(e), _rewrap(e)))
        controls_canvas.configure(yscrollcommand=controls_scroll.set)
        # Always-visible scrollbar for the form column
        controls_scroll.pack(side="right", fill="y")
        controls_canvas.pack(side="left", fill="both", expand=True)
        self._rewrap_controls = _rewrap

        def _controls_wheel(event):
            step = -1 if getattr(event, "num", 0) == 5 or getattr(event, "delta", 0) < 0 else 1
            controls_canvas.yview_scroll(-step, "units")
            return "break"

        def _bind_controls_wheel(widget):
            for sequence in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                widget.bind(sequence, _controls_wheel)
            for child in widget.winfo_children():
                _bind_controls_wheel(child)

        _bind_controls_wheel(controls_canvas)
        _bind_controls_wheel(self.controls)
        # Re-bind after the page finishes building its widgets
        self._preview_bar = None
        self._preview_temp = None
        self.after(200, self._install_preview_button)
        self.after(220, lambda: _bind_controls_wheel(self.controls))
        self.after(240, _rewrap)

        self.preview = PreviewPanel(body)
        body.add(controls_outer, weight=4)
        body.add(self.preview, weight=2)
        self.status_var = tk.StringVar(value="Ready")
        footer = ttk.Frame(self, style="App.TFrame")
        footer.pack(fill="x", pady=(12, 0))
        self.progress = ttk.Progressbar(footer, mode="indeterminate", length=180)
        self.progress.pack(side="left")
        ttk.Label(footer, textvariable=self.status_var, style="Status.TLabel").pack(
            side="left", padx=12
        )

    def section(self, text: str):
        ttk.Label(self.controls, text=text.upper(), style="Eyebrow.TLabel").pack(
            anchor="w", pady=(10, 5)
        )

    # ── Generic "see the result before saving" support ────────────────────
    #
    # A page opts in by defining two things:
    #   preview_source()            -> path of the input PDF (or None)
    #   build_preview_job(tmp_path) -> a zero-argument callable that produces
    #                                  the modified PDF at tmp_path
    # A "Preview result" button is then added automatically.

    def supports_result_preview(self) -> bool:
        return callable(getattr(self, "build_preview_job", None))

    def live_preview_vars(self) -> tuple:
        """Override to name the Tk variables that should trigger an automatic,
        debounced re-preview as the user edits them (checkboxes, text fields,
        sliders). Return an empty tuple to keep the preview manual-only."""
        return ()

    def _install_preview_button(self):
        if not self.supports_result_preview():
            return
        if getattr(self, "_preview_bar", None) is not None:
            return
        live_vars = self.live_preview_vars()

        bar = ttk.Frame(self.controls, style="Panel.TFrame")
        bar.pack(fill="x", pady=(10, 0))
        self.live_preview_enabled = tk.BooleanVar(value=bool(live_vars))
        if live_vars:
            ttk.Checkbutton(
                bar, text="Live preview", variable=self.live_preview_enabled,
                command=lambda: self._schedule_live_preview(force=True),
            ).pack(side="left")
        ttk.Button(
            bar, text="👁  Preview result", command=self.preview_result,
            style="Quiet.TButton",
        ).pack(side="left", padx=(10 if live_vars else 0, 0))
        self.live_preview_status = ttk.Label(bar, text="", style="Help.TLabel")
        self.live_preview_status.pack(side="left", padx=(10, 0))
        ttk.Label(
            self.controls,
            text="Renders the change to a temporary copy shown on the right. "
                 "Your file is not modified until you save.",
            style="Help.TLabel", wraplength=520,
        ).pack(anchor="w", pady=(4, 0))
        self._preview_bar = bar

        if live_vars:
            self._live_preview_job = None
            for variable in live_vars:
                try:
                    variable.trace_add(
                        "write", lambda *_a: self._schedule_live_preview()
                    )
                except Exception:
                    pass

    def _schedule_live_preview(self, force: bool = False):
        """Debounce rapid edits (typing, dragging a slider) into one render."""
        if not self.supports_result_preview():
            return
        if not force and not getattr(self, "live_preview_enabled", tk.BooleanVar(value=False)).get():
            return
        source = None
        try:
            source = self.preview_source()
        except Exception:
            pass
        if not source or not Path(source).is_file():
            return
        job = getattr(self, "_live_preview_job", None)
        if job:
            try:
                self.after_cancel(job)
            except Exception:
                pass
        if hasattr(self, "live_preview_status"):
            self.live_preview_status.configure(text="Updating preview…")
        self._live_preview_job = self.after(500, self.preview_result)

    def _new_preview_path(self) -> str:
        return str(
            Path(tempfile.gettempdir())
            / f"smartpdf_preview_{uuid.uuid4().hex[:10]}.pdf"
        )

    def _discard_preview_temp(self):
        previous = getattr(self, "_preview_temp", None)
        if previous:
            try:
                Path(previous).unlink(missing_ok=True)
            except Exception:
                pass
        self._preview_temp = None

    def preview_result(self):
        """Run the page's operation into a temporary file and display it."""
        if not self.supports_result_preview():
            return
        try:
            source = self.preview_source()
        except Exception as exc:
            messagebox.showwarning(APP_NAME, str(exc), parent=self)
            return
        if not source or not Path(source).is_file():
            messagebox.showwarning(
                APP_NAME, "Select a source PDF first.", parent=self
            )
            return
        temporary = self._new_preview_path()
        try:
            work = self.build_preview_job(temporary)
        except FeatureError as exc:
            messagebox.showwarning(APP_NAME, str(exc), parent=self)
            return
        except Exception as exc:
            messagebox.showwarning(APP_NAME, str(exc), parent=self)
            return
        if work is None:
            return
        self._pending_preview_source = source
        self.run_job(
            "Rendering preview…", work,
            lambda result: self._preview_rendered(result, temporary),
        )

    def _preview_rendered(self, result, temporary: str):
        output = temporary
        if isinstance(result, dict) and result.get("output"):
            output = str(result["output"])
        if not Path(output).is_file():
            messagebox.showwarning(
                APP_NAME, "The preview could not be produced.", parent=self
            )
            return
        self._discard_preview_temp()
        self._preview_temp = output
        page = 0
        if isinstance(result, dict) and result.get("page"):
            page = max(0, int(result["page"]) - 1)
        self.preview.show_comparison(
            getattr(self, "_pending_preview_source", ""), output, page=page
        )
        self.status_var.set(
            "Preview shown — switch Before/After on the right. Nothing saved yet."
        )
        if hasattr(self, "live_preview_status"):
            self.live_preview_status.configure(text="Preview up to date")

    def run_job(self, message: str, work: Callable[[], object], done: Callable[[object], None]):
        self.status_var.set(message)
        self.progress.start(12)

        def runner():
            try:
                result = work()
            except Exception as exc:
                detail = str(exc).strip() or exc.__class__.__name__
                if not isinstance(exc, FeatureError):
                    traceback.print_exc()
                self.after(0, lambda: self._job_failed(detail))
            else:
                self.after(0, lambda: self._job_done(result, done))

        threading.Thread(target=runner, daemon=True).start()

    def _job_failed(self, detail: str):
        self.progress.stop()
        self.status_var.set("Operation failed")
        messagebox.showerror(APP_NAME, detail, parent=self)

    def _job_done(self, result: object, done: Callable[[object], None]):
        self.progress.stop()
        self.status_var.set("Completed successfully")
        # A real save replaces any on-screen "proposed result", so drop the
        # Before/After switch — what is shown is now the actual saved file.
        try:
            output = result.get("output") if isinstance(result, dict) else None
            if output and output != getattr(self, "_preview_temp", None):
                self.preview.clear_comparison()
                self._discard_preview_temp()
        except Exception:
            pass
        done(result)

    def choose_pdf(self, variable: tk.StringVar) -> Optional[str]:
        path = filedialog.askopenfilename(
            parent=self, title="Select PDF", filetypes=[("PDF files", "*.pdf")]
        )
        if path:
            variable.set(path)
            self.preview.load(path)
            return path
        return None

    def preview_path(self, variable: tk.StringVar):
        """Manually preview whatever file path is currently in `variable`."""
        path = variable.get().strip()
        if not path:
            messagebox.showinfo(APP_NAME, "Select a PDF first.", parent=self)
            return
        if not Path(path).is_file():
            messagebox.showwarning(APP_NAME, f"File not found:\n{path}", parent=self)
            return
        try:
            self.preview.load(path)
        except Exception as exc:
            messagebox.showerror(APP_NAME, f"Could not preview this file.\n\n{exc}", parent=self)

    def file_row(self, variable: tk.StringVar, command: Callable, button_text="Browse PDF",
                 show_preview: bool = True):
        row = ttk.Frame(self.controls, style="Panel.TFrame")
        row.pack(fill="x")
        ttk.Entry(row, textvariable=variable).pack(side="left", fill="x", expand=True)
        ttk.Button(row, text=button_text, command=command).pack(side="left", padx=(8, 0))
        if show_preview:
            ttk.Button(
                row, text="👁 Preview", command=lambda: self.preview_path(variable),
                style="Quiet.TButton",
            ).pack(side="left", padx=(6, 0))


class MergePage(BasePage):
    title = "Merge PDFs"
    description = "Combine multiple PDF files in your chosen order into one document."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.files: list[str] = []
        self.section("PDF files")
        self.listbox = tk.Listbox(
            self.controls, height=14, bg=COLORS["paper"], fg=COLORS["ink"],
            selectbackground=COLORS["blue_700"], selectforeground=COLORS["white"], bd=0,
            highlightthickness=1, highlightbackground=COLORS["line"],
            font=("Segoe UI", 10), activestyle="none"
        )
        self.listbox.pack(fill="both", expand=True)
        self.listbox.bind("<<ListboxSelect>>", self._preview_selected)
        buttons = ttk.Frame(self.controls, style="Panel.TFrame")
        buttons.pack(fill="x", pady=8)
        for text, command in (
            ("Add PDFs", self.add_files), ("Remove", self.remove),
            ("Move up", lambda: self.move(-1)), ("Move down", lambda: self.move(1)),
            ("Clear", self.clear), ("👁 Preview Selected", self._preview_selected),
        ):
            ttk.Button(buttons, text=text, command=command, style="Quiet.TButton").pack(
                side="left", padx=(0, 5)
            )
        ttk.Button(
            self.controls, text="Merge and Save PDF", command=self.process, style="Primary.TButton"
        ).pack(fill="x", pady=(12, 0), ipady=4)

    def refresh(self, select: Optional[int] = None):
        self.listbox.delete(0, "end")
        for number, filename in enumerate(self.files, start=1):
            self.listbox.insert("end", f"{number:02d}.  {Path(filename).name}")
        if select is not None and self.files:
            select = max(0, min(select, len(self.files) - 1))
            self.listbox.selection_set(select)
            self.preview.load(self.files[select])

    def add_files(self):
        paths = filedialog.askopenfilenames(
            parent=self, title="Select PDFs", filetypes=[("PDF files", "*.pdf")]
        )
        for path in paths:
            if path not in self.files:
                self.files.append(path)
        self.refresh(len(self.files) - 1 if self.files else None)

    def remove(self):
        selected = self.listbox.curselection()
        if selected:
            del self.files[selected[0]]
            self.refresh(min(selected[0], len(self.files) - 1) if self.files else None)

    def move(self, delta: int):
        selected = self.listbox.curselection()
        if not selected:
            return
        current = selected[0]
        target = current + delta
        if 0 <= target < len(self.files):
            self.files[current], self.files[target] = self.files[target], self.files[current]
            self.refresh(target)

    def clear(self):
        self.files.clear()
        self.refresh()
        self.preview.clear()

    def _preview_selected(self, _event=None):
        selected = self.listbox.curselection()
        if selected:
            self.preview.load(self.files[selected[0]])

    def process(self):
        if len(self.files) < 2:
            messagebox.showwarning(APP_NAME, "Select at least two PDF files.", parent=self)
            return
        default = f"{safe_filename(Path(self.files[0]).stem)}_merged.pdf"
        output = filedialog.asksaveasfilename(
            parent=self, title="Save merged PDF", defaultextension=".pdf",
            initialfile=default, filetypes=[("PDF files", "*.pdf")]
        )
        if not output:
            return
        inputs = tuple(self.files)
        self.run_job(
            "Merging PDFs…", lambda: merge_pdfs(inputs, output),
            lambda result: self._saved(result, "Merged PDF")
        )

    def _saved(self, result, label):
        self.preview.load(result["output"])
        messagebox.showinfo(
            APP_NAME, f"{label} saved successfully.\n\n{result['output']}\nPages: {result['pages']}",
            parent=self,
        )


class CompilerPage(BasePage):
    title = "Compiler"
    description = (
        "Compile an appeal paper book with a master index, exhibit dividers, bookmarks, "
        "continuous pagination, Excel index and reusable project file."
    )

    def __init__(self, master, app):
        super().__init__(master, app)
        self.documents: list[dict] = []
        self.title_var = tk.StringVar(value="APPEAL PAPER BOOK")
        self.case_var = tk.StringVar()
        self.output_name_var = tk.StringVar(value="Appeal_Paper_Book")
        self.output_folder_var = tk.StringVar()
        self.last_index_pdf: Optional[str] = None
        self.last_excel_index: Optional[str] = None
        self.last_compiled_pdf: Optional[str] = None

        self.section("Case and output details")
        details = ttk.Frame(self.controls, style="Panel.TFrame")
        details.pack(fill="x")
        details.columnconfigure(1, weight=1)
        details.columnconfigure(3, weight=1)
        ttk.Label(details, text="Title", style="Panel.TLabel").grid(
            row=0, column=0, sticky="w", padx=(0, 6), pady=3
        )
        ttk.Entry(details, textvariable=self.title_var).grid(
            row=0, column=1, sticky="ew", padx=(0, 10), pady=3
        )
        ttk.Label(details, text="Output name", style="Panel.TLabel").grid(
            row=0, column=2, sticky="w", padx=(0, 6), pady=3
        )
        ttk.Entry(details, textvariable=self.output_name_var).grid(
            row=0, column=3, sticky="ew", pady=3
        )
        ttk.Label(details, text="Case details", style="Panel.TLabel").grid(
            row=1, column=0, sticky="w", padx=(0, 6), pady=3
        )
        ttk.Entry(details, textvariable=self.case_var).grid(
            row=1, column=1, columnspan=3, sticky="ew", pady=3
        )
        ttk.Label(details, text="Output folder", style="Panel.TLabel").grid(
            row=2, column=0, sticky="w", padx=(0, 6), pady=3
        )
        ttk.Entry(details, textvariable=self.output_folder_var).grid(
            row=2, column=1, columnspan=2, sticky="ew", padx=(0, 7), pady=3
        )
        ttk.Button(
            details, text="📁 Browse", command=self.choose_output_folder,
            style="Quiet.TButton"
        ).grid(row=2, column=3, sticky="e", pady=3)

        self.section("Compiler actions — use in sequence")
        action_card = tk.Frame(
            self.controls, bg="#EFF6FF", padx=5, pady=5,
            highlightthickness=1, highlightbackground=COLORS["blue_500"]
        )
        action_card.pack(fill="x", pady=(0, 5))
        action_grid = tk.Frame(action_card, bg="#EFF6FF")
        action_grid.pack(fill="x")
        for column in range(4):
            action_grid.columnconfigure(column, weight=1, uniform="compiler_action")
        actions = (
            ("1  Create Index", self.create_index, COLORS["blue_700"], COLORS["blue_600"]),
            ("2  Index → Excel", self.import_index_to_excel, COLORS["violet"], COLORS["violet_dark"]),
            ("3  Save Compiled", self.save_compiled_file, COLORS["green"], COLORS["green_dark"]),
            ("4  Open Compiled", self.open_compiled_file, COLORS["orange"], COLORS["orange_dark"]),
        )
        for index, (label, command, colour, active_colour) in enumerate(actions):
            tk.Button(
                action_grid, text=label, command=command, bg=colour, fg="white",
                activebackground=active_colour, activeforeground="white", bd=0,
                relief="flat", padx=4, pady=4, font=("Segoe UI", 8, "bold"),
                cursor="hand2"
            ).grid(
                row=0, column=index, sticky="ew", padx=2, pady=0
            )

        self.section("Document controls")
        first_bar = ttk.Frame(self.controls, style="Panel.TFrame")
        first_bar.pack(fill="x", pady=(0, 3))
        for label, command in (
            ("📄 Add PDFs", self.add_pdfs),
            ("📂 Scan Folder", self.scan_folder),
            ("✏ Edit", self.edit_document),
            ("👁 Preview", self.preview_selected),
            ("🗑 Remove", self.remove_documents),
            ("↑ Up", lambda: self.move_document(-1)),
            ("↓ Down", lambda: self.move_document(1)),
        ):
            ttk.Button(
                first_bar, text=label, command=command, style="Compact.TButton"
            ).pack(side="left", padx=(0, 3))
        second_bar = ttk.Frame(self.controls, style="Panel.TFrame")
        second_bar.pack(fill="x", pady=(0, 3))
        for label, command in (
            ("🏷 Auto Exhibits", self.auto_assign_exhibits),
            ("💾 Save Project", self.save_project),
            ("📂 Open Project", self.open_project),
        ):
            ttk.Button(
                second_bar, text=label, command=command, style="Compact.TButton"
            ).pack(side="left", padx=(0, 3))

        self.section("Paper-book documents")
        tree_card = tk.Frame(
            self.controls, bg=COLORS["white"],
            highlightthickness=1, highlightbackground=COLORS["line"]
        )
        tree_card.pack(fill="both", expand=True)
        columns = (
            "order", "exhibit", "ground", "issue", "particulars",
            "pages", "divider", "file"
        )
        self.tree = ttk.Treeview(
            tree_card, columns=columns, show="headings", selectmode="extended",
            height=5, style="Compiler.Treeview"
        )
        headings = {
            "order": "#", "exhibit": "Exhibit", "ground": "Ground",
            "issue": "Issue", "particulars": "Particulars", "pages": "Pages",
            "divider": "Divider", "file": "Source PDF"
        }
        widths = {
            "order": 38, "exhibit": 62, "ground": 70, "issue": 150,
            "particulars": 230, "pages": 52, "divider": 58, "file": 280
        }
        for column in columns:
            self.tree.heading(column, text=headings[column])
            self.tree.column(
                column, width=widths[column], anchor="center" if column in {
                    "order", "exhibit", "ground", "pages", "divider"
                } else "w", stretch=column in {"issue", "particulars", "file"}
            )
        vertical = ttk.Scrollbar(tree_card, orient="vertical", command=self.tree.yview)
        horizontal = ttk.Scrollbar(tree_card, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vertical.set, xscrollcommand=horizontal.set)
        vertical.pack(side="right", fill="y")
        horizontal.pack(side="bottom", fill="x")
        self.tree.pack(side="left", fill="both", expand=True)
        self.tree.bind("<<TreeviewSelect>>", self.preview_selected)
        self.tree.bind("<Double-1>", lambda _event: self.edit_document())

    def choose_output_folder(self):
        folder = filedialog.askdirectory(
            parent=self, title="Select compiler output folder",
            initialdir=self.output_folder_var.get().strip() or None
        )
        if folder:
            self.output_folder_var.set(folder)

    def add_pdfs(self):
        paths = filedialog.askopenfilenames(
            parent=self, title="Add documents to the paper book",
            filetypes=[("PDF files", "*.pdf")]
        )
        added = 0
        for path in paths:
            if self._add_document(path):
                added += 1
        if paths:
            self.refresh(len(self.documents) - 1 if self.documents else None)
            self.status_var.set(f"Added {added} document(s); {len(self.documents)} total")

    def scan_folder(self):
        folder = filedialog.askdirectory(parent=self, title="Select folder containing PDFs")
        if not folder:
            return
        paths = sorted(
            (path for path in Path(folder).iterdir() if path.is_file() and path.suffix.lower() == ".pdf"),
            key=lambda path: path.name.casefold()
        )
        added = sum(1 for path in paths if self._add_document(str(path)))
        self.refresh(len(self.documents) - 1 if self.documents else None)
        self.status_var.set(f"Scanned folder — added {added} PDF(s)")
        if not paths:
            messagebox.showinfo(APP_NAME, "No PDF files were found in that folder.", parent=self)

    def _add_document(self, path: str) -> bool:
        resolved = str(Path(path).resolve())
        normalized = os.path.normcase(resolved)
        if any(os.path.normcase(str(item["path"])) == normalized for item in self.documents):
            return False
        try:
            pages = compiler_page_count(resolved)
        except Exception as exc:
            messagebox.showerror(
                APP_NAME, f"Could not add {Path(path).name}.\n\n{exc}", parent=self
            )
            return False
        stem = Path(resolved).stem
        exhibit = ""
        inferred = re.match(r"^(?:\d+\s*)?([A-Z]+\d*[a-z]?)\s+", stem, re.I)
        if inferred:
            exhibit = inferred.group(1)
        self.documents.append({
            "path": resolved, "exhibit": exhibit, "ground": "", "issue": "",
            "particulars": stem, "remarks": "", "divider": True,
            "page_count": pages,
        })
        return True

    def refresh(self, select: Optional[int] = None):
        self.tree.delete(*self.tree.get_children())
        for index, document in enumerate(self.documents):
            self.tree.insert(
                "", "end", iid=str(index),
                values=(
                    index + 1, document.get("exhibit", ""), document.get("ground", ""),
                    document.get("issue", ""), document.get("particulars", ""),
                    document.get("page_count", ""),
                    "Yes" if document.get("divider", True) else "No",
                    document.get("path", ""),
                )
            )
        if select is not None and self.documents:
            target = max(0, min(select, len(self.documents) - 1))
            self.tree.selection_set(str(target))
            self.tree.focus(str(target))
            self.tree.see(str(target))
            path = self.documents[target].get("path", "")
            if Path(path).is_file():
                self.preview.load(path)

    def selected_indices(self) -> list[int]:
        return sorted(int(item) for item in self.tree.selection())

    def preview_selected(self, _event=None):
        selected = self.selected_indices()
        if selected:
            path = self.documents[selected[0]].get("path", "")
            if Path(path).is_file():
                self.preview.load(path)
            else:
                self.preview.clear("Source file is missing")

    def remove_documents(self):
        selected = self.selected_indices()
        if not selected:
            messagebox.showwarning(APP_NAME, "Select one or more documents to remove.", parent=self)
            return
        for index in reversed(selected):
            self.documents.pop(index)
        self.refresh(min(selected[0], len(self.documents) - 1) if self.documents else None)
        if not self.documents:
            self.preview.clear()
        self.status_var.set(f"{len(self.documents)} document(s) in the compiler")

    def move_document(self, delta: int):
        selected = self.selected_indices()
        if len(selected) != 1:
            messagebox.showwarning(APP_NAME, "Select exactly one document to move.", parent=self)
            return
        current = selected[0]
        target = current + delta
        if 0 <= target < len(self.documents):
            self.documents[current], self.documents[target] = (
                self.documents[target], self.documents[current]
            )
            self.refresh(target)

    def edit_document(self):
        selected = self.selected_indices()
        if len(selected) != 1:
            messagebox.showwarning(APP_NAME, "Select exactly one document to edit.", parent=self)
            return
        index = selected[0]
        document = self.documents[index]
        dialog = tk.Toplevel(self)
        dialog.title("Edit Compiler Document Details")
        dialog.geometry("650x390")
        dialog.minsize(560, 350)
        dialog.transient(self)
        dialog.grab_set()
        dialog.configure(bg=COLORS["paper"])
        panel = ttk.Frame(dialog, style="Panel.TFrame", padding=18)
        panel.pack(fill="both", expand=True, padx=14, pady=14)
        panel.columnconfigure(1, weight=1)
        variables = {
            key: tk.StringVar(value=str(document.get(key, "")))
            for key in ("exhibit", "ground", "issue", "particulars", "remarks")
        }
        labels = (
            ("Exhibit", "exhibit"), ("Ground No.", "ground"), ("Issue", "issue"),
            ("Particulars", "particulars"), ("Remarks", "remarks")
        )
        for row, (label, key) in enumerate(labels):
            ttk.Label(panel, text=label, style="Panel.TLabel").grid(
                row=row, column=0, sticky="w", padx=(0, 10), pady=6
            )
            ttk.Entry(panel, textvariable=variables[key]).grid(
                row=row, column=1, sticky="ew", pady=6
            )
        divider_var = tk.BooleanVar(value=bool(document.get("divider", True)))
        ttk.Checkbutton(
            panel, text="Insert an exhibit divider page before this document",
            variable=divider_var
        ).grid(row=5, column=1, sticky="w", pady=(6, 10))

        def save_changes():
            for key, variable in variables.items():
                document[key] = variable.get().strip()
            document["divider"] = bool(divider_var.get())
            dialog.destroy()
            self.refresh(index)
            self.status_var.set(f"Updated details for {Path(document['path']).name}")

        ttk.Button(
            panel, text="Save Details", command=save_changes, style="Primary.TButton"
        ).grid(row=6, column=1, sticky="e", pady=(8, 0))

    def auto_assign_exhibits(self):
        if not self.documents:
            messagebox.showwarning(APP_NAME, "Add PDF documents first.", parent=self)
            return
        assigned = 0
        for number, document in enumerate(self.documents, 1):
            if not str(document.get("exhibit") or "").strip():
                document["exhibit"] = str(number)
                assigned += 1
        self.refresh()
        self.status_var.set(f"Assigned {assigned} missing exhibit number(s)")

    def project_data(self) -> dict:
        return {
            "version": "4.5", "title": self.title_var.get().strip() or "APPEAL PAPER BOOK",
            "case_info": self.case_var.get().strip(),
            "output_name": self.output_name_var.get().strip() or "Appeal_Paper_Book",
            "output_folder": self.output_folder_var.get().strip(),
            "documents": [dict(document) for document in self.documents],
        }

    def save_project(self):
        if not self.documents:
            messagebox.showwarning(APP_NAME, "Add at least one PDF document first.", parent=self)
            return
        path = filedialog.asksaveasfilename(
            parent=self, title="Save compiler project", defaultextension=".apbc.json",
            initialfile=f"{compiler_safe_filename(self.output_name_var.get())}_Project.apbc.json",
            filetypes=[("Compiler project", "*.apbc.json"), ("JSON files", "*.json")]
        )
        if not path:
            return
        try:
            Path(path).write_text(json.dumps(self.project_data(), indent=2), encoding="utf-8")
        except Exception as exc:
            messagebox.showerror(APP_NAME, f"Could not save the project.\n\n{exc}", parent=self)
            return
        self.status_var.set(f"Project saved: {Path(path).name}")
        messagebox.showinfo(APP_NAME, f"Compiler project saved successfully.\n\n{path}", parent=self)

    def open_project(self):
        path = filedialog.askopenfilename(
            parent=self, title="Open compiler project",
            filetypes=[("Compiler project", "*.apbc.json"), ("JSON files", "*.json")]
        )
        if not path:
            return
        if self.documents and not messagebox.askyesno(
            APP_NAME, "Opening a project will replace the current compiler list. Continue?",
            parent=self
        ):
            return
        try:
            data = json.loads(Path(path).read_text(encoding="utf-8"))
            documents = data.get("documents")
            if not isinstance(documents, list):
                raise FeatureError("This is not a valid Compiler project file.")
            loaded: list[dict] = []
            missing = 0
            for raw in documents:
                if not isinstance(raw, dict):
                    continue
                document = dict(raw)
                source = Path(str(document.get("path") or ""))
                if source.is_file():
                    try:
                        document["page_count"] = compiler_page_count(source)
                    except Exception:
                        document["page_count"] = "ERR"
                else:
                    document["page_count"] = "Missing"
                    missing += 1
                document.setdefault("divider", True)
                document.setdefault("exhibit", "")
                document.setdefault("ground", "")
                document.setdefault("issue", "")
                document.setdefault("particulars", source.stem)
                document.setdefault("remarks", "")
                loaded.append(document)
        except Exception as exc:
            messagebox.showerror(APP_NAME, f"Could not open the project.\n\n{exc}", parent=self)
            return
        self.title_var.set(str(data.get("title") or "APPEAL PAPER BOOK"))
        self.case_var.set(str(data.get("case_info") or ""))
        self.output_name_var.set(str(data.get("output_name") or "Appeal_Paper_Book"))
        self.output_folder_var.set(str(data.get("output_folder") or ""))
        self.documents = loaded
        self.last_index_pdf = None
        self.last_excel_index = None
        self.last_compiled_pdf = None
        self.refresh(0 if self.documents else None)
        self.status_var.set(
            f"Loaded {len(self.documents)} document(s)" + (f"; {missing} source file(s) missing" if missing else "")
        )
        if missing:
            messagebox.showwarning(
                APP_NAME,
                f"Project loaded, but {missing} source PDF file(s) could not be found. "
                "Restore those files before compiling.", parent=self
            )

    def _compiler_progress(self, message: str):
        self.after(0, lambda text=message: self.status_var.set(text))

    def _validated_project(self) -> Optional[dict]:
        if not self.documents:
            messagebox.showwarning(APP_NAME, "Please add PDF documents first.", parent=self)
            return None
        if not self.output_folder_var.get().strip():
            self.choose_output_folder()
        if not self.output_folder_var.get().strip():
            return None
        missing = [
            str(document.get("path") or "") for document in self.documents
            if not Path(str(document.get("path") or "")).is_file()
        ]
        if missing:
            messagebox.showerror(
                APP_NAME,
                "The following source file is missing:\n\n" + "\n".join(missing[:8]),
                parent=self
            )
            return None
        return self.project_data()

    def _confirm_replace(self, path: Path) -> bool:
        return not path.exists() or messagebox.askyesno(
            APP_NAME,
            f"The following file already exists and will be replaced:\n\n{path.name}\n\nContinue?",
            parent=self,
        )

    def create_index(self):
        project = self._validated_project()
        if not project:
            return
        output_folder = Path(project["output_folder"])
        base_name = compiler_safe_filename(project["output_name"])
        output = output_folder / f"{base_name}_Index.pdf"
        if not self._confirm_replace(output):
            return
        self.run_job(
            "Creating master index PDF…",
            lambda: prepare_paper_book_index(project, output),
            self._index_created,
        )

    def _index_created(self, result: object):
        data = dict(result)  # type: ignore[arg-type]
        self.last_index_pdf = data["output"]
        # Show the index in the preview pane immediately, on page 1,
        # before any dialog steals focus.
        self.preview.set_zoom(1.0)
        self.preview.load(data["output"], page=0)
        self.preview.update_idletasks()
        self.status_var.set(
            f"Index created for {data['documents']} document(s) — "
            f"{data['index_pages']} page(s). Shown in the preview pane."
        )
        self.after(120, lambda: self._offer_open(
            data["output"],
            "Master index created successfully.\n\n"
            f"Index PDF: {data['output']}\n"
            f"Index pages: {data['index_pages']}\n\n"
            "It is now displayed in the preview pane on the right.",
            "Open the index PDF in your default viewer as well?",
        ))

    def _offer_open(self, path: str, message: str, question: str):
        """Report success, then optionally open the file in its native app."""
        if messagebox.askyesno(APP_NAME, f"{message}\n\n{question}", parent=self):
            try:
                open_in_file_manager(path)
            except Exception as exc:
                messagebox.showwarning(APP_NAME, str(exc), parent=self)

    def import_index_to_excel(self):
        project = self._validated_project()
        if not project:
            return
        output_folder = Path(project["output_folder"])
        base_name = compiler_safe_filename(project["output_name"])
        output = output_folder / f"{base_name}_Master_Index.xlsx"
        if not self._confirm_replace(output):
            return
        self.run_job(
            "Importing the master index into Excel…",
            lambda: export_paper_book_index_excel(project, output),
            self._excel_index_created,
        )

    def _excel_index_created(self, result: object):
        data = dict(result)  # type: ignore[arg-type]
        output = data["output"]
        self.last_excel_index = output
        rows = data.get("documents", 0)
        self.status_var.set(f"Excel index created for {rows} document(s) — opening…")

        # Open the workbook straight away; this is what the button promises.
        opened, failure = True, ""
        try:
            open_in_file_manager(output)
        except Exception as exc:
            opened, failure = False, str(exc)[:180]

        if opened:
            self.status_var.set(f"Excel index created and opened — {rows} document(s)")
            messagebox.showinfo(
                APP_NAME,
                "Index exported to Excel and opened.\n\n"
                f"File: {output}\n"
                f"Rows: {rows}\n\n"
                "If Excel did not appear, check behind this window or open the "
                "file from the output folder.",
                parent=self,
            )
        else:
            self.status_var.set(f"Excel index created — {rows} document(s)")
            if messagebox.askyesno(
                APP_NAME,
                "The Excel index was created, but it could not be opened "
                "automatically.\n\n"
                f"File: {output}\n"
                f"Reason: {failure}\n\n"
                "Open the containing folder instead?",
                parent=self,
            ):
                try:
                    open_in_file_manager(str(Path(output).parent))
                except Exception as exc:
                    messagebox.showwarning(APP_NAME, str(exc), parent=self)

    def save_compiled_file(self):
        project = self._validated_project()
        if not project:
            return
        output_folder = Path(project["output_folder"])
        base_name = compiler_safe_filename(project["output_name"])
        output_paths = (
            output_folder / f"{base_name}.pdf",
            output_folder / f"{base_name}_Master_Index.xlsx",
            output_folder / f"{base_name}_Project.apbc.json",
        )
        existing = [path.name for path in output_paths if path.exists()]
        if existing and not messagebox.askyesno(
            APP_NAME,
            "The following output file(s) already exist and will be replaced:\n\n"
            + "\n".join(existing) + "\n\nContinue?",
            parent=self
        ):
            return
        self.run_job(
            "Compiling appeal paper book…",
            lambda: compile_paper_book(project, self._compiler_progress),
            self._compiled,
        )

    def compile(self):
        """Backward-compatible alias for the separated Save Compiled File action."""
        self.save_compiled_file()

    def open_compiled_file(self):
        candidate: Optional[Path] = None
        if self.last_compiled_pdf and Path(self.last_compiled_pdf).is_file():
            candidate = Path(self.last_compiled_pdf)
        else:
            folder = self.output_folder_var.get().strip()
            if folder:
                expected = Path(folder) / (
                    compiler_safe_filename(self.output_name_var.get()) + ".pdf"
                )
                if expected.is_file():
                    candidate = expected
        if candidate is None:
            selected = filedialog.askopenfilename(
                parent=self, title="Open compiled paper book",
                initialdir=self.output_folder_var.get().strip() or None,
                filetypes=[("PDF files", "*.pdf")]
            )
            if not selected:
                return
            candidate = Path(selected)
        try:
            open_in_file_manager(candidate)
            self.preview.load(str(candidate))
            self.status_var.set(f"Opened compiled file: {candidate.name}")
        except Exception as exc:
            messagebox.showerror(
                APP_NAME, f"Could not open the compiled file.\n\n{exc}", parent=self
            )

    def _compiled(self, result: object):
        data = dict(result)  # type: ignore[arg-type]
        self.last_compiled_pdf = data["pdf"]
        self.last_excel_index = data["excel"]
        self.preview.load(data["pdf"])
        self.status_var.set(
            f"Compiled {data['documents']} document(s) into {data['pages']} pages"
        )
        messagebox.showinfo(
            APP_NAME,
            "✅ Paper book compiled successfully.\n\n"
            f"PDF: {data['pdf']}\n"
            f"Excel index: {data['excel']}\n"
            f"Project: {data['project']}\n\n"
            f"Total pages: {data['pages']}\n\n"
            "Use ‘Open Compiled File’ to open the completed PDF.",
            parent=self,
        )


class DownloaderPage(BasePage):
    title = "PDF Downloader"
    description = (
        "Find linked and embedded PDF files on a webpage, then download them safely "
        "without overwriting existing files."
    )

    def __init__(self, master, app):
        super().__init__(master, app)
        base_folder = (
            Path(sys.executable).resolve().parent if getattr(sys, "frozen", False)
            else Path(__file__).resolve().parent
        )
        self.url_var = tk.StringVar()
        self.output_folder_var = tk.StringVar(value=str(base_folder / "Downloaded_PDFs"))
        self.count_var = tk.StringVar(value="No webpage scanned")
        self.links: list[str] = []
        self.busy = False

        self.section("Webpage URL")
        url_row = ttk.Frame(self.controls, style="Panel.TFrame")
        url_row.pack(fill="x")
        self.url_entry = ttk.Entry(url_row, textvariable=self.url_var)
        self.url_entry.pack(side="left", fill="x", expand=True)
        self.url_entry.bind("<Return>", lambda _event: self.scan_webpage())
        tk.Button(
            url_row, text="🔍 Scan Website", command=self.scan_webpage,
            bg=COLORS["blue_700"], fg="white", activebackground=COLORS["blue_600"],
            activeforeground="white", bd=0, relief="flat", padx=12, pady=8,
            font=("Segoe UI", 9, "bold"), cursor="hand2"
        ).pack(side="left", padx=(7, 0))
        ttk.Label(
            self.controls,
            text="Example: https://example.com/resources — regular links, embeds, iframes and object tags are scanned.",
            style="Help.TLabel", wraplength=650
        ).pack(anchor="w", pady=(4, 7))

        self.section("Download folder")
        folder_row = ttk.Frame(self.controls, style="Panel.TFrame")
        folder_row.pack(fill="x")
        ttk.Entry(folder_row, textvariable=self.output_folder_var).pack(
            side="left", fill="x", expand=True
        )
        ttk.Button(
            folder_row, text="📁 Browse", command=self.choose_folder,
            style="Quiet.TButton"
        ).pack(side="left", padx=(7, 0))
        ttk.Button(
            folder_row, text="Open", command=self.open_folder,
            style="Quiet.TButton"
        ).pack(side="left", padx=(5, 0))

        found_header = ttk.Frame(self.controls, style="Panel.TFrame")
        found_header.pack(fill="x", pady=(11, 5))
        ttk.Label(found_header, text="FOUND PDF LINKS", style="Eyebrow.TLabel").pack(side="left")
        ttk.Label(found_header, textvariable=self.count_var, style="Help.TLabel").pack(side="right")
        link_frame = tk.Frame(
            self.controls, bg=COLORS["white"],
            highlightthickness=1, highlightbackground=COLORS["line"]
        )
        link_frame.pack(fill="both", expand=True)
        link_scroll = ttk.Scrollbar(link_frame, orient="vertical")
        self.link_list = tk.Listbox(
            link_frame, bg=COLORS["blue_050"], fg=COLORS["ink"], bd=0,
            selectbackground=COLORS["blue_700"], selectforeground="white",
            font=("Segoe UI", 9), activestyle="none", yscrollcommand=link_scroll.set,
            height=8
        )
        link_scroll.configure(command=self.link_list.yview)
        link_scroll.pack(side="right", fill="y")
        self.link_list.pack(side="left", fill="both", expand=True)
        self.link_list.bind("<Double-1>", self.copy_selected_link)

        action_row = ttk.Frame(self.controls, style="Panel.TFrame")
        action_row.pack(fill="x", pady=(8, 6))
        tk.Button(
            action_row, text="⬇️  Download All PDFs", command=self.download_all,
            bg=COLORS["green"], fg="white", activebackground=COLORS["green_dark"],
            activeforeground="white", bd=0, relief="flat", padx=14, pady=8,
            font=("Segoe UI", 9, "bold"), cursor="hand2"
        ).pack(side="left", fill="x", expand=True, padx=(0, 5))
        ttk.Button(
            action_row, text="👁 Preview Selected", command=self.preview_selected_link,
            style="Quiet.TButton",
        ).pack(side="left", padx=(0, 5))
        tk.Button(
            action_row, text="🗑 Clear", command=self.clear,
            bg=COLORS["red"], fg="white", activebackground=COLORS["red_dark"],
            activeforeground="white", bd=0, relief="flat", padx=12, pady=8,
            font=("Segoe UI", 9, "bold"), cursor="hand2"
        ).pack(side="right")

        self.section("Activity log")
        log_frame = tk.Frame(
            self.controls, bg=COLORS["white"],
            highlightthickness=1, highlightbackground=COLORS["line"]
        )
        log_frame.pack(fill="x")
        log_scroll = ttk.Scrollbar(log_frame, orient="vertical")
        self.log_box = tk.Text(
            log_frame, height=6, bg="#0F2740", fg="#E6F1FB", bd=0,
            font=("Consolas", 8), wrap="word", padx=8, pady=6,
            yscrollcommand=log_scroll.set, state="disabled"
        )
        log_scroll.configure(command=self.log_box.yview)
        log_scroll.pack(side="right", fill="y")
        self.log_box.pack(side="left", fill="both", expand=True)
        self._append_log("Ready. Enter a webpage URL and click Scan Website.")

    def choose_folder(self):
        folder = filedialog.askdirectory(
            parent=self, title="Select PDF download folder",
            initialdir=self.output_folder_var.get().strip() or None
        )
        if folder:
            self.output_folder_var.set(folder)

    def open_folder(self):
        folder = Path(self.output_folder_var.get().strip()).expanduser()
        try:
            folder.mkdir(parents=True, exist_ok=True)
            open_in_file_manager(folder)
        except Exception as exc:
            messagebox.showerror(APP_NAME, f"Could not open the folder.\n\n{exc}", parent=self)

    def _append_log(self, message: str):
        timestamp = datetime.now().strftime("%H:%M:%S")
        self.log_box.configure(state="normal")
        self.log_box.insert("end", f"[{timestamp}] {message}\n")
        self.log_box.see("end")
        self.log_box.configure(state="disabled")

    def _thread_log(self, message: str):
        self.after(0, lambda text=message: self._append_log(text))

    def _start_task(self, message: str, work: Callable[[], object],
                    done: Callable[[object], None], determinate: bool = False):
        if self.busy:
            messagebox.showinfo(APP_NAME, "Please wait for the current operation to finish.", parent=self)
            return
        self.busy = True
        self.status_var.set(message)
        if determinate:
            self.progress.stop()
            self.progress.configure(mode="determinate", value=0, maximum=max(1, len(self.links)))
        else:
            self.progress.configure(mode="indeterminate")
            self.progress.start(12)

        def runner():
            try:
                result = work()
            except Exception as exc:
                detail = str(exc).strip() or exc.__class__.__name__
                if not isinstance(exc, FeatureError):
                    traceback.print_exc()
                self.after(0, lambda text=detail: self._task_failed(text))
            else:
                self.after(0, lambda value=result: self._task_done(value, done))

        threading.Thread(target=runner, daemon=True).start()

    def _task_failed(self, detail: str):
        self.busy = False
        self.progress.stop()
        self.progress.configure(mode="indeterminate", value=0)
        self.status_var.set("Operation failed")
        self._append_log(f"ERROR: {detail}")
        messagebox.showerror(APP_NAME, detail, parent=self)

    def _task_done(self, result: object, done: Callable[[object], None]):
        self.busy = False
        self.progress.stop()
        self.progress.configure(mode="indeterminate", value=0)
        done(result)

    def scan_webpage(self):
        if self.busy:
            return
        try:
            url = normalize_webpage_url(self.url_var.get())
        except FeatureError as exc:
            messagebox.showwarning(APP_NAME, str(exc), parent=self)
            return
        self.url_var.set(url)
        self.links.clear()
        self.link_list.delete(0, "end")
        self.count_var.set("Scanning…")
        self._append_log("Starting webpage scan.")
        self._start_task(
            "Scanning webpage for PDF links…",
            lambda: discover_pdf_links(url, self._thread_log),
            self._scan_complete,
        )

    def _scan_complete(self, result: object):
        data = dict(result)  # type: ignore[arg-type]
        self.links = list(data.get("links") or [])
        for number, link in enumerate(self.links, 1):
            self.link_list.insert("end", f"{number:03d}.  {link}")
        self.count_var.set(f"{len(self.links)} PDF(s) found")
        self.status_var.set(f"Scan complete — {len(self.links)} PDF link(s) found")
        if not self.links:
            messagebox.showinfo(
                APP_NAME,
                "No direct or embedded PDF links were found on this webpage.\n\n"
                "Some websites create download links with JavaScript or require sign-in; "
                "those links cannot be discovered from the public page HTML.",
                parent=self,
            )

    def _download_progress(self, current: int, total: int, message: str):
        self.after(0, lambda: self._set_download_progress(current, total, message))

    def _set_download_progress(self, current: int, total: int, message: str):
        self.progress.configure(maximum=max(1, total), value=current)
        self.status_var.set(message)

    def download_all(self):
        if not self.links:
            messagebox.showwarning(APP_NAME, "Scan a webpage and find PDF links first.", parent=self)
            return
        folder = self.output_folder_var.get().strip()
        if not folder:
            self.choose_folder()
            folder = self.output_folder_var.get().strip()
        if not folder:
            return
        links = tuple(self.links)
        self._append_log(f"Starting download of {len(links)} PDF file(s).")
        self._start_task(
            f"Downloading {len(links)} PDF file(s)…",
            lambda: download_pdf_links(
                links, folder, self._download_progress, self._thread_log,
                referer=self.url_var.get().strip()
            ),
            self._download_complete,
            determinate=True,
        )

    def _download_complete(self, result: object):
        data = dict(result)  # type: ignore[arg-type]
        downloaded = list(data.get("downloaded") or [])
        failed = list(data.get("failed") or [])
        self.status_var.set(
            f"Downloaded {len(downloaded)} PDF(s); {len(failed)} failed"
        )
        if downloaded:
            self.preview.load(downloaded[0])
        self._append_log(
            f"Finished: {len(downloaded)} downloaded, {len(failed)} failed."
        )
        message = (
            f"PDF download completed.\n\nDownloaded: {len(downloaded)}\n"
            f"Failed: {len(failed)}\nFolder: {data.get('folder', '')}"
        )
        if failed:
            message += "\n\nReview the activity log for failed links."
        messagebox.showinfo(APP_NAME, message, parent=self)

    def copy_selected_link(self, _event=None):
        selection = self.link_list.curselection()
        if not selection:
            return
        link = self.links[selection[0]]
        self.clipboard_clear()
        self.clipboard_append(link)
        self.status_var.set("PDF link copied to clipboard")

    def preview_selected_link(self):
        selection = self.link_list.curselection()
        if not selection:
            messagebox.showinfo(APP_NAME, "Select a link from the list first.", parent=self)
            return
        link = self.links[selection[0]]
        folder = Path(self.output_folder_var.get().strip() or ".").expanduser()
        expected_name = unquote(Path(urlparse(link).path).name) or ""
        candidate = folder / expected_name if expected_name else None
        if candidate and candidate.is_file():
            self.preview.load(str(candidate))
            return
        # Fall back to any PDF already downloaded in this session with a similar name.
        if folder.is_dir() and expected_name:
            stem = Path(expected_name).stem.casefold()
            matches = [p for p in folder.glob("*.pdf") if stem and stem in p.stem.casefold()]
            if matches:
                self.preview.load(str(matches[0]))
                return
        messagebox.showinfo(
            APP_NAME,
            "This PDF has not been downloaded yet — click 'Download All PDFs' first, "
            "then preview it.",
            parent=self,
        )

    def clear(self):
        if self.busy:
            messagebox.showinfo(APP_NAME, "Please wait for the current operation to finish.", parent=self)
            return
        self.links.clear()
        self.link_list.delete(0, "end")
        self.url_var.set("")
        self.count_var.set("No webpage scanned")
        self.log_box.configure(state="normal")
        self.log_box.delete("1.0", "end")
        self.log_box.configure(state="disabled")
        self._append_log("Cleared. Ready for a new webpage.")
        self.preview.clear()
        self.status_var.set("Ready")


class SplitPage(BasePage):
    title = "Split PDF"
    description = "Split by page, fixed-size chunks, equal parts, selected pages, or custom groups."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.mode_var = tk.StringVar(value="Every page")
        self.value_var = tk.StringVar()
        self.section("Source PDF")
        self.file_row(self.file_var, lambda: self.choose_pdf(self.file_var))
        self.section("Split method")
        modes = ("Every page", "Every N pages", "Equal parts", "Selected pages (one PDF)", "Custom groups")
        combo = ttk.Combobox(self.controls, textvariable=self.mode_var, values=modes, state="readonly")
        combo.pack(fill="x")
        combo.bind("<<ComboboxSelected>>", self._mode_changed)
        self.hint_var = tk.StringVar(value="Creates one PDF for each page.")
        ttk.Label(self.controls, textvariable=self.hint_var, style="Help.TLabel", wraplength=520).pack(
            anchor="w", pady=(5, 8)
        )
        self.value_entry = ttk.Entry(self.controls, textvariable=self.value_var)
        self.value_entry.pack(fill="x")
        self.value_entry.state(["disabled"])
        ttk.Button(
            self.controls, text="Split and Choose Output Folder", command=self.process,
            style="Primary.TButton"
        ).pack(fill="x", pady=(18, 0), ipady=4)

    def _mode_changed(self, _event=None):
        mode = self.mode_var.get()
        hints = {
            "Every page": "Creates one PDF for each page.",
            "Every N pages": "Enter pages per output file, e.g. 5.",
            "Equal parts": "Enter the number of approximately equal output files.",
            "Selected pages (one PDF)": "Enter pages such as 1-3,5,8-10.",
            "Custom groups": "Separate output groups with semicolons, e.g. 1-3; 4,6; 5,7-9.",
        }
        self.hint_var.set(hints[mode])
        self.value_entry.state(["disabled"] if mode == "Every page" else ["!disabled"])

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a source PDF.", parent=self)
            return
        folder = filedialog.askdirectory(parent=self, title="Choose output folder")
        if not folder:
            return
        mode = self.mode_var.get()
        value = self.value_var.get()
        self.run_job(
            "Splitting PDF…",
            lambda: split_pdf(source, folder, mode, value),
            self._done,
        )

    def _done(self, result):
        outputs = result.get("outputs") or []
        if outputs:
            self.preview.load(outputs[0])
        messagebox.showinfo(
            APP_NAME,
            f"Created {result['count']} PDF file(s).\n\nSaved in:\n{result['folder']}",
            parent=self,
        )


@dataclass
class PageItem:
    source: int
    rotation: int = 0


class OrganizePage(BasePage):
    title = "Organize Pages"
    description = "Reorder, remove, and rotate pages before saving a new PDF."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.items: list[PageItem] = []
        self.section("Source PDF")
        self.file_row(self.file_var, self.load_pdf)
        self.section("Page order")
        self.listbox = tk.Listbox(
            self.controls, height=14, bg=COLORS["paper"], fg=COLORS["ink"],
            selectbackground=COLORS["blue_700"], selectforeground=COLORS["white"], bd=0,
            highlightthickness=1, highlightbackground=COLORS["line"], font=("Segoe UI", 10)
        )
        self.listbox.pack(fill="both", expand=True)
        self.listbox.bind("<<ListboxSelect>>", self.show_page)
        row = ttk.Frame(self.controls, style="Panel.TFrame")
        row.pack(fill="x", pady=8)
        for text, command in (
            ("Up", lambda: self.move(-1)), ("Down", lambda: self.move(1)),
            ("Rotate left", lambda: self.rotate(-90)), ("Rotate right", lambda: self.rotate(90)),
            ("Remove", self.remove),
        ):
            ttk.Button(row, text=text, command=command, style="Quiet.TButton").pack(
                side="left", padx=(0, 4)
            )
        ttk.Button(
            self.controls, text="Save Organized PDF", command=self.process, style="Primary.TButton"
        ).pack(fill="x", pady=(10, 0), ipady=4)

    def load_pdf(self):
        source = self.choose_pdf(self.file_var)
        if not source:
            return
        try:
            pymupdf = get_pymupdf()
            doc = pymupdf.open(source)
            if doc.needs_pass:
                raise FeatureError("This PDF is password-protected.")
            self.items = [PageItem(index) for index in range(doc.page_count)]
            doc.close()
            self.refresh(0)
        except Exception as exc:
            messagebox.showerror(APP_NAME, str(exc), parent=self)

    def refresh(self, select: Optional[int] = None):
        self.listbox.delete(0, "end")
        for position, item in enumerate(self.items, start=1):
            rotation = f"  •  {item.rotation % 360}°" if item.rotation % 360 else ""
            self.listbox.insert("end", f"{position:03d}. Source page {item.source + 1}{rotation}")
        if select is not None and self.items:
            select = max(0, min(select, len(self.items) - 1))
            self.listbox.selection_set(select)
            self.preview.load(self.file_var.get(), self.items[select].source)

    def selected(self) -> Optional[int]:
        values = self.listbox.curselection()
        return values[0] if values else None

    def show_page(self, _event=None):
        index = self.selected()
        if index is not None:
            self.preview.load(self.file_var.get(), self.items[index].source)

    def move(self, delta: int):
        current = self.selected()
        if current is None:
            return
        target = current + delta
        if 0 <= target < len(self.items):
            self.items[current], self.items[target] = self.items[target], self.items[current]
            self.refresh(target)

    def rotate(self, amount: int):
        current = self.selected()
        if current is not None:
            self.items[current].rotation = (self.items[current].rotation + amount) % 360
            self.refresh(current)

    def remove(self):
        current = self.selected()
        if current is not None:
            del self.items[current]
            self.refresh(min(current, len(self.items) - 1) if self.items else None)

    def preview_source(self):
        return self.file_var.get().strip()

    def build_preview_job(self, temporary):
        if not self.items:
            raise FeatureError("Keep at least one page in the layout.")
        source = self.preview_source()
        plan = tuple((item.source, item.rotation) for item in self.items)
        return lambda: organize_pdf(source, temporary, plan)

    def process(self):
        source = self.file_var.get()
        if not Path(source).is_file() or not self.items:
            messagebox.showwarning(APP_NAME, "Load a PDF and keep at least one page.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save organized PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_organized.pdf",
            filetypes=[("PDF files", "*.pdf")]
        )
        if not output:
            return
        plan = tuple((item.source, item.rotation) for item in self.items)
        self.run_job(
            "Organizing pages…", lambda: organize_pdf(source, output, plan),
            lambda result: self._saved(result)
        )

    def _saved(self, result):
        self.preview.load(result["output"])
        messagebox.showinfo(APP_NAME, f"Organized PDF saved.\n\n{result['output']}", parent=self)


class WatermarkPage(BasePage):
    title = "Watermark PDF"
    description = "Apply a text or image watermark to all pages or selected page ranges."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.kind_var = tk.StringVar(value="Text")
        self.text_var = tk.StringVar(value="CONFIDENTIAL")
        self.image_var = tk.StringVar()
        self.pages_var = tk.StringVar()
        self.position_var = tk.StringVar(value="Centre")
        self.opacity_var = tk.DoubleVar(value=0.25)
        self.rotation_var = tk.DoubleVar(value=45)
        self.size_var = tk.DoubleVar(value=48)
        self.tiled_var = tk.BooleanVar(value=False)

        self.section("Source PDF")
        self.file_row(self.file_var, lambda: self.choose_pdf(self.file_var))
        self.section("Watermark")
        kind_row = ttk.Frame(self.controls, style="Panel.TFrame")
        kind_row.pack(fill="x")
        for value in ("Text", "Image"):
            ttk.Radiobutton(
                kind_row, text=value, value=value, variable=self.kind_var,
                command=self._kind_changed
            ).pack(side="left", padx=(0, 12))
        self.input_host = ttk.Frame(self.controls, style="Panel.TFrame")
        self.input_host.pack(fill="x", pady=(7, 0))
        self.text_entry = ttk.Entry(self.input_host, textvariable=self.text_var)
        self.text_entry.pack(fill="x", pady=(7, 0))
        self.image_row = ttk.Frame(self.input_host, style="Panel.TFrame")
        ttk.Entry(self.image_row, textvariable=self.image_var).pack(side="left", fill="x", expand=True)
        ttk.Button(self.image_row, text="Browse image", command=self.choose_image).pack(side="left", padx=(8, 0))

        grid = ttk.Frame(self.controls, style="Panel.TFrame")
        grid.pack(fill="x", pady=(12, 0))
        for column in range(2):
            grid.columnconfigure(column, weight=1)
        self._field(grid, "Pages (blank = all)", ttk.Entry(grid, textvariable=self.pages_var), 0, 0)
        self._field(
            grid, "Position",
            ttk.Combobox(grid, textvariable=self.position_var, values=tuple(POSITIONS), state="readonly"),
            0, 1,
        )
        self._field(grid, "Opacity (0.05–1.0)", ttk.Spinbox(grid, from_=0.05, to=1, increment=.05, textvariable=self.opacity_var), 1, 0)
        self._field(grid, "Rotation", ttk.Spinbox(grid, from_=-180, to=180, increment=5, textvariable=self.rotation_var), 1, 1)
        self.size_label = ttk.Label(grid, text="Text size (points)", style="Panel.TLabel")
        self.size_label.grid(row=4, column=0, sticky="w", padx=(0, 8), pady=(8, 3))
        ttk.Spinbox(grid, from_=8, to=200, increment=2, textvariable=self.size_var).grid(
            row=5, column=0, sticky="ew", padx=(0, 8)
        )
        ttk.Checkbutton(grid, text="Tile across each page", variable=self.tiled_var).grid(
            row=5, column=1, sticky="w", padx=(8, 0)
        )
        ttk.Button(
            self.controls, text="Apply Watermark and Save", command=self.process,
            style="Primary.TButton"
        ).pack(fill="x", pady=(18, 0), ipady=4)

    def _field(self, parent, label, widget, row, column):
        padx = (0, 8) if column == 0 else (8, 0)
        ttk.Label(parent, text=label, style="Panel.TLabel").grid(
            row=row * 2, column=column, sticky="w", padx=padx, pady=(8, 3)
        )
        widget.grid(row=row * 2 + 1, column=column, sticky="ew", padx=padx)

    def _kind_changed(self):
        if self.kind_var.get() == "Text":
            self.image_row.pack_forget()
            self.text_entry.pack(fill="x")
            self.size_label.configure(text="Text size (points)")
            if self.size_var.get() <= 1:
                self.size_var.set(48)
        else:
            self.text_entry.pack_forget()
            self.image_row.pack(fill="x")
            self.size_label.configure(text="Image width (% of page)")
            self.size_var.set(30)

    def choose_image(self):
        path = filedialog.askopenfilename(
            parent=self, title="Select watermark image",
            filetypes=[("Images", "*.png *.jpg *.jpeg")]
        )
        if path:
            self.image_var.set(path)

    def _watermark_args(self, source: str, output: str):
        content = (
            self.text_var.get() if self.kind_var.get() == "Text"
            else self.image_var.get()
        )
        return (
            source, output, self.kind_var.get(), content, self.pages_var.get(),
            self.position_var.get(), float(self.opacity_var.get()),
            float(self.rotation_var.get()), float(self.size_var.get()),
            bool(self.tiled_var.get()),
        )

    def preview_watermark(self):
        """Render the watermark onto a temporary copy and show it on the right."""
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a source PDF first.", parent=self)
            return
        if self.kind_var.get() == "Text" and not self.text_var.get().strip():
            messagebox.showwarning(APP_NAME, "Enter the watermark text.", parent=self)
            return
        if self.kind_var.get() == "Image" and not Path(self.image_var.get()).is_file():
            messagebox.showwarning(APP_NAME, "Choose a watermark image.", parent=self)
            return
        temporary = str(
            Path(tempfile.gettempdir()) / f"smartpdf_wm_{uuid.uuid4().hex[:8]}.pdf"
        )
        args = self._watermark_args(source, temporary)
        self.run_job(
            "Rendering watermark preview…",
            lambda: add_watermark(*args),
            self._preview_ready,
        )

    def _preview_ready(self, result):
        previous = getattr(self, "_preview_temp", None)
        self._preview_temp = result["output"]
        try:
            self.preview.set_zoom(1.0)
        except Exception:
            pass
        self.preview.load(result["output"], page=0)
        self.status_var.set(
            "Preview only — nothing saved yet. Use 'Apply Watermark and Save' to keep it."
        )
        if previous and previous != result["output"]:
            try:
                Path(previous).unlink(missing_ok=True)
            except Exception:
                pass

    def live_preview_vars(self) -> tuple:
        return (
            self.file_var, self.kind_var, self.text_var, self.image_var,
            self.pages_var, self.position_var, self.opacity_var,
            self.rotation_var, self.size_var, self.tiled_var,
        )

    def preview_source(self):
        return self.file_var.get().strip()

    def build_preview_job(self, temporary):
        if self.kind_var.get() == "Text" and not self.text_var.get().strip():
            raise FeatureError("Enter the watermark text.")
        if self.kind_var.get() == "Image" and not Path(self.image_var.get()).is_file():
            raise FeatureError("Choose a watermark image.")
        args = self._watermark_args(self.preview_source(), temporary)
        return lambda: add_watermark(*args)

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a source PDF.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save watermarked PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_watermarked.pdf",
            filetypes=[("PDF files", "*.pdf")]
        )
        if not output:
            return
        args = self._watermark_args(source, output)
        self.run_job(
            "Applying watermark…", lambda: add_watermark(*args),
            lambda result: self._saved(result)
        )

    def _saved(self, result):
        self.preview.load(result["output"])
        messagebox.showinfo(
            APP_NAME, f"Watermark applied to {result['pages']} page(s).\n\n{result['output']}",
            parent=self,
        )


class ConvertPage(BasePage):
    title = "Convert Documents"
    description = "Convert PDF, Word, Excel, PNG, and JPEG files locally on your computer."

    CONVERSIONS = (
        # From PDF
        "PDF → Word (.docx)", "PDF → Excel (.xlsx)", "PDF → PowerPoint (.pptx)",
        "PDF → JPG images", "PDF → PNG images", "PDF → Markdown (.md)",
        "PDF → PDF/A (archival)",
        # To PDF
        "Word (.docx) → PDF", "Excel (.xlsx) → PDF", "PowerPoint (.pptx) → PDF",
        "Images (JPG/PNG) → PDF", "HTML file → PDF", "Web page (URL) → PDF",
    )

    def __init__(self, master, app):
        super().__init__(master, app)
        self.files: list[str] = []
        self.conversion_var = tk.StringVar(value=self.CONVERSIONS[0])
        self.ocr_var = tk.BooleanVar(value=False)
        self.section("Conversion")
        combo = ttk.Combobox(
            self.controls, textvariable=self.conversion_var, values=self.CONVERSIONS,
            state="readonly"
        )
        combo.pack(fill="x")
        combo.bind("<<ComboboxSelected>>", lambda _e: self._conversion_changed())
        self.section("Input")
        self.file_label = tk.StringVar(value="No file selected")
        ttk.Label(
            self.controls, textvariable=self.file_label, style="Help.TLabel", wraplength=500
        ).pack(anchor="w", pady=(0, 7))
        self.choose_button = ttk.Button(
            self.controls, text="Choose input file", command=self.choose_input
        )
        self.choose_button.pack(fill="x")
        # URL entry (shown only for "Web page (URL) → PDF")
        self.url_var = tk.StringVar()
        self.url_row = ttk.Frame(self.controls, style="Panel.TFrame")
        ttk.Label(self.url_row, text="Web page address", style="Panel.TLabel").pack(anchor="w", pady=(0, 3))
        ttk.Entry(self.url_row, textvariable=self.url_var).pack(fill="x")
        ttk.Label(
            self.url_row, text="Example: https://www.incometax.gov.in",
            style="Help.TLabel",
        ).pack(anchor="w", pady=(4, 0))
        self.ocr_check = ttk.Checkbutton(
            self.controls, text="Use OCR for scanned PDFs (requires Tesseract)", variable=self.ocr_var
        )
        self.ocr_check.pack(anchor="w", pady=(12, 0))
        ttk.Button(
            self.controls, text="Convert and Save", command=self.process, style="Primary.TButton"
        ).pack(fill="x", pady=(18, 0), ipady=4)

    MULTI_IMAGE = "Images (JPG/PNG) → PDF"
    URL_MODE = "Web page (URL) → PDF"

    def _conversion_changed(self):
        self.files.clear()
        self.url_var.set("")
        self.file_label.set("No file selected")
        self.preview.clear()
        conversion = self.conversion_var.get()
        # OCR only helps when reading FROM a PDF
        if conversion.startswith("PDF →"):
            self.ocr_check.pack(anchor="w", pady=(12, 0))
        else:
            self.ocr_check.pack_forget()
        # URL entry replaces the file chooser for web pages
        if conversion == self.URL_MODE:
            self.choose_button.pack_forget()
            self.url_row.pack(fill="x")
        else:
            self.url_row.pack_forget()
            self.choose_button.pack(fill="x")

    def choose_input(self):
        conversion = self.conversion_var.get()
        if conversion == self.MULTI_IMAGE:
            paths = filedialog.askopenfilenames(
                parent=self, title="Select images in page order",
                filetypes=[("Images", "*.png *.jpg *.jpeg *.tif *.tiff *.bmp *.webp")],
            )
            self.files = list(paths)
        else:
            if conversion.startswith("PDF"):
                types = [("PDF files", "*.pdf")]
            elif conversion.startswith("Word"):
                types = [("Word documents", "*.docx *.doc")]
            elif conversion.startswith("Excel"):
                types = [("Excel workbooks", "*.xlsx *.xlsm *.xls")]
            elif conversion.startswith("PowerPoint"):
                types = [("PowerPoint files", "*.pptx *.ppt")]
            elif conversion.startswith("HTML"):
                types = [("HTML files", "*.html *.htm")]
            else:
                types = [("All files", "*.*")]
            path = filedialog.askopenfilename(parent=self, title="Select input", filetypes=types)
            self.files = [path] if path else []
        if self.files:
            self.file_label.set(
                Path(self.files[0]).name if len(self.files) == 1
                else f"{len(self.files)} file(s) selected"
            )
            if Path(self.files[0]).suffix.lower() == ".pdf":
                self.preview.load(self.files[0])

    def process(self):
        conversion = self.conversion_var.get()
        use_ocr = bool(self.ocr_var.get())

        # --- Web page (URL) → PDF ---
        if conversion == self.URL_MODE:
            url = self.url_var.get().strip()
            if not url:
                messagebox.showwarning(APP_NAME, "Enter a web page address.", parent=self)
                return
            if not url.lower().startswith(("http://", "https://")):
                url = "https://" + url
            output = filedialog.asksaveasfilename(
                parent=self, title="Save PDF", defaultextension=".pdf",
                initialfile="webpage.pdf", filetypes=[("PDF files", "*.pdf")],
            )
            if not output:
                return
            self.run_job(
                "Downloading and converting…",
                lambda: html_to_pdf(url, output, is_url=True),
                self._converted,
            )
            return

        if not self.files:
            messagebox.showwarning(APP_NAME, "Choose an input file.", parent=self)
            return
        source = self.files[0]
        stem = safe_filename(Path(source).stem)

        # --- PDF → image folder ---
        if conversion in ("PDF → PNG images", "PDF → JPG images"):
            folder = filedialog.askdirectory(parent=self, title="Choose image output folder")
            if not folder:
                return
            fmt = "png" if "PNG" in conversion else "jpeg"
            self.run_job(
                "Converting document…",
                lambda: pdf_to_images(source, folder, fmt),
                self._converted,
            )
            return

        # --- Everything else writes a single output file ---
        extensions = {
            "PDF → Word (.docx)": ".docx",
            "PDF → Excel (.xlsx)": ".xlsx",
            "PDF → PowerPoint (.pptx)": ".pptx",
            "PDF → Markdown (.md)": ".md",
        }
        extension = extensions.get(conversion, ".pdf")
        suffix = "_archival" if "PDF/A" in conversion else "_converted"
        output = filedialog.asksaveasfilename(
            parent=self, title="Save converted file", defaultextension=extension,
            initialfile=f"{stem}{suffix}{extension}",
            filetypes=[("Output file", f"*{extension}")],
        )
        if not output:
            return

        jobs = {
            "PDF → Word (.docx)":       lambda: pdf_to_word(source, output, use_ocr),
            "PDF → Excel (.xlsx)":      lambda: pdf_to_excel(source, output, use_ocr),
            "PDF → PowerPoint (.pptx)": lambda: pdf_to_powerpoint(source, output),
            "PDF → Markdown (.md)":     lambda: pdf_to_markdown(source, output, use_ocr),
            "PDF → PDF/A (archival)":   lambda: pdf_to_pdfa(source, output),
            "Word (.docx) → PDF":       lambda: word_to_pdf(source, output),
            "Excel (.xlsx) → PDF":      lambda: excel_to_pdf(source, output),
            "PowerPoint (.pptx) → PDF": lambda: powerpoint_to_pdf(source, output),
            "HTML file → PDF":          lambda: html_to_pdf(source, output, is_url=False),
            self.MULTI_IMAGE:           lambda: images_to_pdf(tuple(self.files), output),
        }
        work = jobs.get(conversion)
        if work is None:
            messagebox.showerror(APP_NAME, f"Unknown conversion: {conversion}", parent=self)
            return
        self.run_job("Converting document…", work, self._converted)

    def _converted(self, result):
        output = str(result.get("output", ""))
        if output.lower().endswith(".pdf"):
            try:
                self.preview.load(output)
            except Exception:
                pass
        if "folder" in result:
            detail = f"Created {result['count']} image(s).\n\n{result['folder']}"
        else:
            mode = f"\nMode: {result['mode']}" if result.get("mode") else ""
            pages = f"\nPages: {result['pages']}" if result.get("pages") else ""
            detail = f"Converted file saved.\n\n{output}{mode}{pages}"
        messagebox.showinfo(APP_NAME, detail, parent=self)
        if result.get("warning"):
            messagebox.showwarning(APP_NAME, result["warning"], parent=self)


class TranslatePage(BasePage):
    title = "Translate PDF"
    description = "Translate Indian and international-language PDFs to English or from English into another language."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.source_var = tk.StringVar(value="Auto detect")
        self.target_var = tk.StringVar(value="English")
        self.ocr_var = tk.BooleanVar(value=False)
        self.bilingual_var = tk.BooleanVar(value=False)
        self.engine_var = tk.StringVar(value="offline")
        self.pack_status_var = tk.StringVar()
        detected_tesseract = find_tesseract_executable() or ""
        self.tesseract_var = tk.StringVar(value=detected_tesseract)
        self.tesseract_status_var = tk.StringVar()

        self.section("Source PDF")
        self.file_row(self.file_var, lambda: self.choose_pdf(self.file_var))

        self.section("Translation engine")
        engine_row = ttk.Frame(self.controls, style="Panel.TFrame")
        engine_row.pack(fill="x")
        ttk.Radiobutton(
            engine_row, text="Offline  —  runs on this PC",
            variable=self.engine_var, value="offline", command=self._on_engine_change,
        ).pack(anchor="w", pady=2)
        ttk.Radiobutton(
            engine_row, text="Online  —  needs internet",
            variable=self.engine_var, value="online", command=self._on_engine_change,
        ).pack(anchor="w", pady=2)
        ttk.Label(
            self.controls,
            text="Offline mode currently covers English, Hindi, Bengali, Urdu, Arabic, Chinese, "
                 "Japanese, French, German and Spanish. Marathi, Gujarati, Tamil, Telugu, Kannada, "
                 "Malayalam, Punjabi, Odia, Assamese, Sanskrit and Nepali need Online mode.",
            style="Help.TLabel", wraplength=510,
        ).pack(anchor="w", pady=(4, 0))
        pack_row = ttk.Frame(self.controls, style="Panel.TFrame")
        pack_row.pack(fill="x", pady=(8, 0))
        ttk.Button(
            pack_row, text="Download language pack",
            command=self.download_pack, style="Quiet.TButton",
        ).pack(side="left")
        ttk.Button(
            pack_row, text="Install downloaded pack (.argosmodel file)…",
            command=self.install_pack_from_file, style="Quiet.TButton",
        ).pack(side="left", padx=(8, 0))
        ttk.Label(
            self.controls,
            text="Offline uses Argos Translate with locally installed packs \u2014 nothing "
                 "is sent over the internet. Online uses Google/MyMemory and covers all "
                 "21 languages, but transmits the extracted text.",
            style="Help.TLabel", wraplength=520,
        ).pack(anchor="w", pady=(4, 0))
        self.pack_status_label = ttk.Label(
            self.controls, textvariable=self.pack_status_var, style="Help.TLabel"
        )
        self.pack_status_label.pack(anchor="w", pady=(6, 0))

        self.section("Languages")
        language_row = ttk.Frame(self.controls, style="Panel.TFrame")
        language_row.pack(fill="x")
        language_row.columnconfigure(0, weight=1)
        language_row.columnconfigure(2, weight=1)
        ttk.Label(language_row, text="From", style="Panel.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(language_row, text="To", style="Panel.TLabel").grid(row=0, column=2, sticky="w")
        source_box = ttk.Combobox(
            language_row, textvariable=self.source_var, values=tuple(LANGUAGES), state="readonly"
        )
        source_box.grid(row=1, column=0, sticky="ew", pady=(4, 0))
        source_box.bind("<<ComboboxSelected>>", lambda _e: self._refresh_pack_status())
        ttk.Button(
            language_row, text="⇄", command=self.swap_languages, style="Round.TButton", width=3
        ).grid(row=1, column=1, padx=9, pady=(4, 0))
        target_values = tuple(name for name in LANGUAGES if name != "Auto detect")
        target_box = ttk.Combobox(
            language_row, textvariable=self.target_var, values=target_values, state="readonly"
        )
        target_box.grid(row=1, column=2, sticky="ew", pady=(4, 0))
        target_box.bind("<<ComboboxSelected>>", lambda _e: self._refresh_pack_status())

        options = ttk.Frame(self.controls, style="Panel.TFrame")
        options.pack(fill="x", pady=(16, 0))
        ttk.Checkbutton(
            options,
            text="Use OCR (scanned PDFs only)",
            variable=self.ocr_var,
        ).pack(anchor="w", pady=2)
        ttk.Checkbutton(
            options,
            text="Bilingual output",
            variable=self.bilingual_var,
        ).pack(anchor="w", pady=2)
        ttk.Label(
            options,
            text="Tick OCR only for scanned/image-only PDFs \u2014 selectable-text PDFs do not "
                 "need it. Bilingual output places the original text beneath each translation.",
            style="Help.TLabel", wraplength=520,
        ).pack(anchor="w", pady=(4, 0))
        ocr_path_row = ttk.Frame(options, style="Panel.TFrame")
        ocr_path_row.pack(fill="x", pady=(9, 0))
        ttk.Entry(ocr_path_row, textvariable=self.tesseract_var).pack(
            side="left", fill="x", expand=True
        )
        ttk.Button(
            ocr_path_row, text="Locate Tesseract", command=self.browse_tesseract,
            style="Quiet.TButton"
        ).pack(side="left", padx=(8, 0))
        self.tesseract_status_label = ttk.Label(
            options, textvariable=self.tesseract_status_var, style="Help.TLabel"
        )
        self.tesseract_status_label.pack(anchor="w", pady=(4, 0))
        self._refresh_tesseract_status()

        self.notice = tk.Frame(
            self.controls, bg=COLORS["blue_050"], highlightthickness=1,
            highlightbackground=COLORS["blue_200"], padx=13, pady=11,
        )
        self.notice.pack(fill="x", pady=(15, 0))
        self.notice_label = tk.Label(
            self.notice, bg=COLORS["blue_050"], fg=COLORS["blue_800"],
            font=("Segoe UI", 9), justify="left", wraplength=490,
        )
        self.notice_label.pack(anchor="w")
        self._refresh_pack_status()
        self._on_engine_change()
        ttk.Label(
            self.controls,
            text="The translated PDF is clean and reflowed; exact source formatting is not retained. "
                 "Selectable-text PDFs do not require Tesseract. For scanned PDFs, install the "
                 "relevant Tesseract language pack.",
            style="Help.TLabel", wraplength=510,
        ).pack(anchor="w", pady=(10, 0))
        ttk.Button(
            self.controls,
            text="Translate and Save PDF",
            command=self.process,
            style="Primary.TButton",
        ).pack(fill="x", pady=(18, 0), ipady=4)

    def _on_engine_change(self):
        if self.engine_var.get() == "offline":
            self.notice_label.configure(
                text="Offline mode: extracted text is translated entirely on this PC using "
                     "installed Argos Translate language packs. Nothing is sent over the internet."
            )
        else:
            self.notice_label.configure(
                text="Privacy notice: extracted text is sent to the selected online translation "
                     "service. Do not use this mode for confidential documents unless permitted."
            )
        self._refresh_pack_status()

    def download_pack(self):
        source_name, target_name = self.source_var.get(), self.target_var.get()
        source_code = LANGUAGES.get(source_name, "auto")
        target_code = LANGUAGES.get(target_name, "en")
        if source_code == "auto":
            messagebox.showinfo(
                APP_NAME,
                "Select a specific 'From' language before downloading a pack "
                "(auto-detect cannot be pre-downloaded).",
                parent=self,
            )
            return
        if not (argos_is_language_supported(source_code) and argos_is_language_supported(target_code)):
            messagebox.showwarning(APP_NAME, ARGOS_UNSUPPORTED_NOTE, parent=self)
            return

        def work():
            ensure_argos_pair_installed(source_code, target_code, log=None)
            return {"source": source_name, "target": target_name}

        def done(result):
            self._refresh_pack_status()
            messagebox.showinfo(
                APP_NAME,
                f"Language pack ready for {result['source']} ⇄ {result['target']}.\n\n"
                "Translation for this pair now works fully offline.",
                parent=self,
            )

        self.run_job(f"Downloading {source_name} ⇄ {target_name} language pack…", work, done)

    def install_pack_from_file(self):
        file_path = filedialog.askopenfilename(
            parent=self,
            title="Select the downloaded .argosmodel file",
            filetypes=[("Argos Translate package", "*.argosmodel"), ("All files", "*.*")],
        )
        if not file_path:
            return

        def work():
            return argos_install_from_file(file_path)

        def done(result):
            self._refresh_pack_status()
            languages = ", ".join(result.get("installed_languages") or []) or "none detected"
            messagebox.showinfo(
                APP_NAME,
                f"Installed: {Path(file_path).name}\n\n"
                f"Offline languages now available: {languages}\n\n"
                "If your chosen 'From'/'To' pair still shows as not installed above, "
                "you may also need the matching English leg (e.g. installing Hindi→English "
                "does not by itself install English→Hindi).",
                parent=self,
            )

        self.run_job(f"Installing {Path(file_path).name}…", work, done)

    def _refresh_pack_status(self):
        if self.engine_var.get() != "offline":
            self.pack_status_var.set("")
            return
        if not _module_available("argostranslate"):
            self.pack_status_var.set(
                "\u2717 Offline engine not installed.  Run:  "
                f"{sys.executable} -m pip install argostranslate"
            )
            self.pack_status_label.configure(foreground=COLORS["danger"])
            return
        source_code = LANGUAGES.get(self.source_var.get(), "auto")
        target_code = LANGUAGES.get(self.target_var.get(), "en")
        if not (argos_is_language_supported(source_code)
                and argos_is_language_supported(target_code)):
            self.pack_status_var.set(
                "\u26a0 This language is not available offline. Switch to the Online engine."
            )
            self.pack_status_label.configure(foreground=COLORS["warning"])
            return
        ready, reason = argos_pair_ready(source_code, target_code)
        try:
            installed = sorted(argos_installed_language_codes())
        except Exception:
            installed = []
        have = ", ".join(installed) if installed else "none"
        if ready:
            self.pack_status_var.set(
                f"\u2714 Ready to translate offline. Installed packs: {have}"
            )
            self.pack_status_label.configure(foreground=COLORS["success"])
        else:
            self.pack_status_var.set(
                f"\u2717 Not ready \u2014 {reason}  (installed: {have})\n"
                "Use 'Download language pack', or 'Install downloaded pack' if your "
                "network blocks the download."
            )
            self.pack_status_label.configure(foreground=COLORS["danger"])

    def swap_languages(self):
        source, target = self.source_var.get(), self.target_var.get()
        if source == "Auto detect":
            self.source_var.set(target)
            self.target_var.set("English" if target != "English" else "Hindi / हिन्दी")
        else:
            self.source_var.set(target)
            self.target_var.set(source)
        self._refresh_pack_status()

    def browse_tesseract(self):
        path = filedialog.askopenfilename(
            parent=self,
            title="Locate Tesseract OCR executable",
            filetypes=[
                ("Tesseract executable", "tesseract.exe"),
                ("Executable files", "*.exe"),
                ("All files", "*.*"),
            ],
        )
        if path:
            self.tesseract_var.set(path)
            self._refresh_tesseract_status()

    def _refresh_tesseract_status(self):
        custom = self.tesseract_var.get().strip()
        executable = find_tesseract_executable(custom)
        if executable:
            self.tesseract_var.set(executable)
            installed = get_available_tesseract_langs(executable)
            if installed:
                names = [TESSERACT_LANG_NAMES.get(c, c) for c in installed]
                lang_line = ", ".join(names[:8])
                if len(names) > 8:
                    lang_line += f" (+{len(names)-8} more)"
                self.tesseract_status_var.set(
                    f"✔ OCR ready  |  Installed packs: {lang_line}"
                )
                self.tesseract_status_label.configure(foreground=COLORS["success"])
            else:
                self.tesseract_status_var.set(
                    "⚠ Tesseract found but NO language packs installed. "
                    "Re-run the installer and tick the required languages."
                )
                self.tesseract_status_label.configure(foreground=COLORS["warning"])
        else:
            self.tesseract_status_var.set(
                "ℹ Tesseract not detected — fine for selectable-text PDFs. "
                "Only needed for scanned/image-only PDFs."
            )
            self.tesseract_status_label.configure(foreground=COLORS["muted"])

    def process(self):
        source_path = self.file_var.get().strip()
        if not Path(source_path).is_file():
            messagebox.showwarning(APP_NAME, "Select a source PDF.", parent=self)
            return
        source_name, target_name = self.source_var.get(), self.target_var.get()
        source_code, target_code = LANGUAGES[source_name], LANGUAGES[target_name]
        if source_code == target_code and source_code != "auto":
            messagebox.showwarning(APP_NAME, "Source and target languages must be different.", parent=self)
            return
        engine = self.engine_var.get()
        if engine == "offline" and not (
            argos_is_language_supported(source_code) and argos_is_language_supported(target_code)
        ):
            messagebox.showwarning(APP_NAME, ARGOS_UNSUPPORTED_NOTE, parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self,
            title="Save translated PDF",
            defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source_path).stem)}_{target_code}_translated.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        use_ocr = bool(self.ocr_var.get())
        bilingual = bool(self.bilingual_var.get())
        tesseract_path = self.tesseract_var.get().strip() or None

        # Pre-flight: if OCR is on, verify the language pack is actually installed
        if use_ocr:
            source_code_check = LANGUAGES.get(source_name, "auto")
            tess_code_check = TESSERACT_LANGUAGES.get(source_code_check, "eng")
            installed_packs = get_available_tesseract_langs(tesseract_path)
            if installed_packs and tess_code_check not in installed_packs:
                lang_name_friendly = TESSERACT_LANG_NAMES.get(tess_code_check, tess_code_check)
                packs_str = ", ".join(installed_packs)
                answer = messagebox.askyesno(
                    APP_NAME,
                    f"The '{tess_code_check}' ({lang_name_friendly}) Tesseract language pack "
                    f"is NOT installed on this machine.\n\n"
                    f"Installed packs: {packs_str}\n\n"
                    f"HOW TO FIX:\n"
                    f"  • Download {tess_code_check}.traineddata from:\n"
                    f"    https://github.com/tesseract-ocr/tessdata/raw/main/{tess_code_check}.traineddata\n"
                    f"  • Save it to your Tesseract 'tessdata' folder\n"
                    f"    (e.g. C:\\Program Files\\Tesseract-OCR\\tessdata\\)\n\n"
                    "Do you want to proceed anyway (translation may fail)?",
                    parent=self,
                )
                if not answer:
                    return

        self.run_job(
            f"Translating to {target_name}…",
            lambda: translate_pdf(
                source_path, output, source_code, target_code, use_ocr, bilingual,
                tesseract_path, engine=engine
            ),
            self._translated,
        )

    def _translated(self, result):
        self.preview.load(result["output"])
        messagebox.showinfo(
            APP_NAME,
            f"Translation completed.\n\n"
            f"{result['source']} → {result['target']}\n"
            f"Pages: {result['pages']}\n\n{result['output']}",
            parent=self,
        )


class CompressPage(BasePage):
    title = "Compress PDF"
    description = "Optimize PDF streams and optionally recompress embedded images."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.level_var = tk.StringVar(value="Medium")
        self.section("Source PDF")
        self.file_row(self.file_var, lambda: self.choose_pdf(self.file_var))
        self.section("Compression level")
        for value, description in (
            ("Low", "Lossless structural optimization; best quality."),
            ("Medium", "Recompress images up to 1,800 px at JPEG quality 70."),
            ("High", "Recompress images up to 1,200 px at JPEG quality 45."),
        ):
            line = ttk.Frame(self.controls, style="Panel.TFrame")
            line.pack(fill="x", pady=3)
            ttk.Radiobutton(line, text=value, value=value, variable=self.level_var).pack(side="left")
            ttk.Label(line, text=description, style="Help.TLabel").pack(side="left", padx=8)
        ttk.Button(
            self.controls, text="Compress and Save", command=self.process, style="Primary.TButton"
        ).pack(fill="x", pady=(18, 0), ipady=4)

    def preview_source(self):
        return self.file_var.get().strip()

    def build_preview_job(self, temporary):
        source, level = self.preview_source(), self.level_var.get()
        return lambda: compress_pdf(source, temporary, level)

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a source PDF.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save compressed PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_compressed.pdf",
            filetypes=[("PDF files", "*.pdf")]
        )
        if not output:
            return
        level = self.level_var.get()
        self.run_job(
            "Compressing PDF…", lambda: compress_pdf(source, output, level),
            lambda result: self._saved(result)
        )

    def _saved(self, result):
        self.preview.load(result["output"])
        messagebox.showinfo(
            APP_NAME,
            "Compression completed.\n\n"
            f"Original: {human_size(result['original'])}\n"
            f"Output: {human_size(result['compressed'])}\n"
            f"Reduction: {result['reduction']:.1f}%\n\n{result['output']}",
            parent=self,
        )


class CertificateEntryDialog(tk.Toplevel):
    """Collect the settings for one digital signature certificate."""

    def __init__(self, master, page_count: int, existing: Optional[dict] = None):
        super().__init__(master)
        self.title("Digital signature certificate")
        self.configure(bg=COLORS["panel"])
        self.resizable(False, False)
        self.transient(master)
        self.result: Optional[dict] = None
        data = existing or {}

        self.path_var = tk.StringVar(value=data.get("path", ""))
        self.password_var = tk.StringVar(value=data.get("password", ""))
        self.name_var = tk.StringVar(value=data.get("signer_name", ""))
        self.reason_var = tk.StringVar(value=data.get("reason", ""))
        self.location_var = tk.StringVar(value=data.get("location", ""))
        self.visible_var = tk.BooleanVar(value=data.get("visible", True))
        self.scope_var = tk.StringVar(value=data.get("scope", "Last page only"))
        self.pages_var = tk.StringVar(value=data.get("pages_text", ""))
        self.position_var = tk.StringVar(value=data.get("position", "Bottom right"))
        box = data.get("custom_box") or (380, 40, 560, 110)
        self.x0_var = tk.DoubleVar(value=box[0])
        self.y0_var = tk.DoubleVar(value=box[1])
        self.x1_var = tk.DoubleVar(value=box[2])
        self.y1_var = tk.DoubleVar(value=box[3])

        body = ttk.Frame(self, style="Panel.TFrame", padding=18)
        body.pack(fill="both", expand=True)

        def section(text):
            ttk.Label(body, text=text.upper(), style="Eyebrow.TLabel").pack(
                anchor="w", pady=(12, 5)
            )

        section("Certificate file (.pfx / .p12)")
        row = ttk.Frame(body, style="Panel.TFrame")
        row.pack(fill="x")
        ttk.Entry(row, textvariable=self.path_var, width=46).pack(
            side="left", fill="x", expand=True
        )
        ttk.Button(row, text="Browse", style="Quiet.TButton",
                   command=self.browse).pack(side="left", padx=(8, 0))

        section("Certificate password")
        ttk.Entry(body, textvariable=self.password_var, show="●").pack(fill="x")

        section("Signer details")
        grid = ttk.Frame(body, style="Panel.TFrame")
        grid.pack(fill="x")
        grid.columnconfigure(1, weight=1)
        for row_index, (label, variable) in enumerate((
            ("Signer name", self.name_var),
            ("Reason", self.reason_var),
            ("Location", self.location_var),
        )):
            ttk.Label(grid, text=label, style="Panel.TLabel").grid(
                row=row_index, column=0, sticky="w", pady=3, padx=(0, 10)
            )
            ttk.Entry(grid, textvariable=variable).grid(
                row=row_index, column=1, sticky="ew", pady=3
            )

        section(f"Which pages to sign  (document has {page_count} page(s))")
        ttk.Combobox(
            body, textvariable=self.scope_var, state="readonly",
            values=SIGNATURE_SCOPES,
        ).pack(fill="x")
        self.pages_entry = ttk.Entry(body, textvariable=self.pages_var)
        self.pages_hint = ttk.Label(
            body, text="Page numbers, e.g. 1,3,5-7", style="Help.TLabel"
        )
        self.scope_var.trace_add("write", lambda *_: self._scope_changed())

        section("Signature appearance")
        ttk.Checkbutton(
            body, text="Visible signature stamp on the page",
            variable=self.visible_var, command=self._visible_changed,
        ).pack(anchor="w")
        self.position_combo = ttk.Combobox(
            body, textvariable=self.position_var, state="readonly",
            values=tuple(SIGNATURE_POSITIONS),
        )
        self.position_combo.pack(fill="x", pady=(8, 0))
        self.position_var.trace_add("write", lambda *_: self._position_changed())

        self.custom_frame = ttk.Frame(body, style="Panel.TFrame")
        ttk.Label(
            self.custom_frame,
            text="Custom box in PDF points, measured from the bottom-left corner "
                 "(A4 is 595 × 842).",
            style="Help.TLabel", wraplength=440,
        ).pack(anchor="w", pady=(6, 4))
        custom_grid = ttk.Frame(self.custom_frame, style="Panel.TFrame")
        custom_grid.pack(fill="x")
        for column, (label, variable) in enumerate((
            ("X from", self.x0_var), ("Y from", self.y0_var),
            ("X to", self.x1_var), ("Y to", self.y1_var),
        )):
            custom_grid.columnconfigure(column, weight=1)
            ttk.Label(custom_grid, text=label, style="Panel.TLabel").grid(
                row=0, column=column, sticky="w", padx=(0, 6)
            )
            ttk.Spinbox(
                custom_grid, from_=0, to=2000, increment=5,
                textvariable=variable, width=8,
            ).grid(row=1, column=column, sticky="ew", padx=(0, 6))

        buttons = ttk.Frame(body, style="Panel.TFrame")
        buttons.pack(fill="x", pady=(18, 0))
        ttk.Button(buttons, text="Cancel", style="Quiet.TButton",
                   command=self.destroy).pack(side="right")
        ttk.Button(buttons, text="Save certificate", style="Primary.TButton",
                   command=self.confirm).pack(side="right", padx=(0, 8))

        self._scope_changed()
        self._visible_changed()
        self._position_changed()
        self.grab_set()
        self.wait_window(self)

    def _scope_changed(self):
        if self.scope_var.get() == "Selected pages":
            self.pages_entry.pack(fill="x", pady=(8, 0))
            self.pages_hint.pack(anchor="w", pady=(3, 0))
        else:
            self.pages_entry.pack_forget()
            self.pages_hint.pack_forget()

    def _visible_changed(self):
        if self.visible_var.get():
            self.position_combo.state(["!disabled"])
        else:
            self.position_combo.state(["disabled"])
            self.custom_frame.pack_forget()

    def _position_changed(self):
        if self.position_var.get() == "Custom" and self.visible_var.get():
            self.custom_frame.pack(fill="x", pady=(8, 0))
        else:
            self.custom_frame.pack_forget()

    def browse(self):
        path = filedialog.askopenfilename(
            parent=self, title="Select PKCS#12 certificate",
            filetypes=[("PKCS#12 certificate", "*.pfx *.p12"), ("All files", "*.*")],
        )
        if path:
            self.path_var.set(path)
            if not self.name_var.get().strip():
                self.name_var.set(Path(path).stem)

    def confirm(self):
        if not Path(self.path_var.get().strip()).is_file():
            messagebox.showwarning(APP_NAME, "Select a certificate file.", parent=self)
            return
        if self.scope_var.get() == "Selected pages" and not self.pages_var.get().strip():
            messagebox.showwarning(
                APP_NAME, "Enter the page numbers to sign.", parent=self
            )
            return
        self.result = {
            "path": self.path_var.get().strip(),
            "password": self.password_var.get(),
            "signer_name": self.name_var.get().strip(),
            "reason": self.reason_var.get().strip(),
            "location": self.location_var.get().strip(),
            "visible": bool(self.visible_var.get()),
            "scope": self.scope_var.get(),
            "pages_text": self.pages_var.get().strip(),
            "position": self.position_var.get(),
            "custom_box": (
                float(self.x0_var.get()), float(self.y0_var.get()),
                float(self.x1_var.get()), float(self.y1_var.get()),
            ),
        }
        self.destroy()


class UnprotectPage(BasePage):
    title = "Unprotect PDF"
    description = (
        "Remove printing, copying and editing restrictions from a PDF you are "
        "authorised to use."
    )

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.password_var = tk.StringVar()

        self.section("Restricted PDF")
        row = ttk.Frame(self.controls, style="Panel.TFrame")
        row.pack(fill="x")
        ttk.Entry(row, textvariable=self.file_var).pack(
            side="left", fill="x", expand=True
        )
        ttk.Button(row, text="Browse PDF", command=self.choose).pack(
            side="left", padx=(8, 0)
        )

        self.section("Current restrictions")
        self.report = tk.Text(
            self.controls, height=9, bg=COLORS["blue_050"], fg=COLORS["ink"], bd=0,
            highlightthickness=1, highlightbackground=COLORS["line"],
            font=("Consolas", 9), wrap="word", padx=10, pady=8,
        )
        self.report.pack(fill="x")
        self.report.insert("1.0", "Select a PDF to inspect its restrictions.")
        self.report.configure(state="disabled")

        self.section("Open password (only if the PDF asks for one)")
        ttk.Entry(self.controls, textvariable=self.password_var, show="●").pack(fill="x")
        ttk.Label(
            self.controls,
            text="Many restricted PDFs open without any password — they carry only an "
                 "owner password. Leave this blank in that case.",
            style="Help.TLabel", wraplength=520,
        ).pack(anchor="w", pady=(4, 0))

        notice = tk.Frame(self.controls, bg=COLORS["blue_100"], padx=13, pady=11)
        notice.pack(fill="x", pady=(14, 0))
        tk.Label(
            notice,
            text="Use this only on documents you own or are authorised to modify. "
                 "It removes restriction flags; it does not defeat an unknown open "
                 "password. Unlock PDF removes a known open password instead.",
            bg=COLORS["blue_100"], fg=COLORS["blue_900"], font=("Segoe UI", 9),
            justify="left", wraplength=500,
        ).pack(anchor="w")

        ttk.Button(
            self.controls, text="Remove Restrictions and Save",
            command=self.process, style="Primary.TButton",
        ).pack(fill="x", pady=(16, 0), ipady=4)

    def _write(self, text: str):
        self.report.configure(state="normal")
        self.report.delete("1.0", "end")
        self.report.insert("1.0", text)
        self.report.configure(state="disabled")

    def choose(self):
        path = filedialog.askopenfilename(
            parent=self, title="Select restricted PDF",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not path:
            return
        self.file_var.set(path)
        try:
            info = pdf_restrictions(path)
        except Exception as exc:
            self._write(f"Could not inspect this PDF.\n\n{exc}")
            return
        lines = [
            f"Encrypted        : {'yes' if info['encrypted'] else 'no'}",
            f"Open password    : {'required' if info['needs_password'] else 'not required'}",
        ]
        if info.get("permissions"):
            lines.append("")
            lines.append("Currently allowed:")
            labels = {
                "print": "Printing", "copy": "Copying text/images",
                "modify": "Editing content", "annotate": "Annotating",
                "form_fill": "Filling forms", "assemble": "Assembling pages",
                "extract_accessibility": "Accessibility extraction",
            }
            for key, allowed in info["permissions"].items():
                mark = "yes" if allowed else "NO"
                lines.append(f"  {labels.get(key, key):26} {mark}")
            lines.append("")
            lines.append(
                "This PDF is restricted — removing restrictions will help."
                if info.get("restricted")
                else "This PDF already permits every action; nothing to remove."
            )
        self._write("\n".join(lines))
        if not info["needs_password"]:
            try:
                self.preview.load(path)
            except Exception:
                pass

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a PDF file.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save unrestricted PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_unrestricted.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        password = self.password_var.get()
        self.run_job(
            "Removing restrictions…",
            lambda: unprotect_pdf(source, output, password),
            self._done,
        )

    def _done(self, result):
        self.preview.load(result["output"])
        info = pdf_restrictions(result["output"])
        allowed = info.get("permissions", {})
        self._write(
            f"Restrictions removed.\n\n"
            f"Pages            : {result['pages']}\n"
            f"Was encrypted    : {'yes' if result['was_encrypted'] else 'no'}\n"
            f"Still encrypted  : {'yes' if result['still_encrypted'] else 'no'}\n\n"
            "All actions now permitted: "
            f"{'yes' if all(allowed.values()) else 'no'}"
        )
        messagebox.showinfo(
            APP_NAME,
            "Restrictions removed successfully.\n\n"
            f"Pages: {result['pages']}\n{result['output']}",
            parent=self,
        )


class SignPage(BasePage):
    title = "Digital Signature"
    description = (
        "Apply one or more digital signatures (DSC) with control over which pages "
        "are signed and where each stamp appears."
    )

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.page_count = 0
        self.certificates: list[dict] = []

        self.section("PDF to sign")
        row = ttk.Frame(self.controls, style="Panel.TFrame")
        row.pack(fill="x")
        ttk.Entry(row, textvariable=self.file_var).pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Browse PDF", command=self.choose_source).pack(
            side="left", padx=(8, 0)
        )
        self.info_var = tk.StringVar(value="No PDF selected")
        ttk.Label(self.controls, textvariable=self.info_var, style="Help.TLabel").pack(
            anchor="w", pady=(5, 0)
        )

        self.section("Signature certificates — signed in this order")
        columns = ("signer", "certificate", "pages", "placement")
        self.tree = ttk.Treeview(
            self.controls, columns=columns, show="headings", height=6
        )
        headings = {
            "signer": ("Signer", 150), "certificate": ("Certificate", 130),
            "pages": ("Pages", 110), "placement": ("Placement", 120),
        }
        for key in columns:
            text, width = headings[key]
            self.tree.heading(key, text=text)
            self.tree.column(key, width=width, anchor="w", stretch=True)
        tree_scroll = ttk.Scrollbar(
            self.controls, orient="vertical", command=self.tree.yview
        )
        self.tree.configure(yscrollcommand=tree_scroll.set)
        self.tree.pack(fill="x", side="top")

        buttons = ttk.Frame(self.controls, style="Panel.TFrame")
        buttons.pack(fill="x", pady=(8, 0))
        for text, command in (
            ("Add certificate", self.add_certificate),
            ("Edit", self.edit_certificate),
            ("Remove", self.remove_certificate),
            ("Move up", lambda: self.move(-1)),
            ("Move down", lambda: self.move(1)),
        ):
            ttk.Button(buttons, text=text, command=command, style="Quiet.TButton").pack(
                side="left", padx=(0, 5)
            )

        ttk.Label(
            self.controls,
            text="Each certificate can sign a different set of pages and use a "
                 "different stamp position. Signatures are applied as incremental "
                 "updates, so earlier signatures stay valid.",
            style="Help.TLabel", wraplength=520,
        ).pack(anchor="w", pady=(10, 0))

        self.section("Test certificate")
        ttk.Button(
            self.controls, text="Create a self-signed test certificate",
            command=self.make_test_certificate, style="Quiet.TButton",
        ).pack(anchor="w")
        ttk.Label(
            self.controls,
            text="For trials only. Statutory filings require a DSC issued by a "
                 "licensed Certifying Authority.",
            style="Help.TLabel", wraplength=520,
        ).pack(anchor="w", pady=(4, 0))

        actions = ttk.Frame(self.controls, style="Panel.TFrame")
        actions.pack(fill="x", pady=(16, 0))
        ttk.Button(
            actions, text="Sign and Save PDF", command=self.process,
            style="Primary.TButton",
        ).pack(side="left", fill="x", expand=True, ipady=4)
        ttk.Button(
            actions, text="Verify signatures", command=self.verify,
            style="Quiet.TButton",
        ).pack(side="left", padx=(8, 0))

    # ── helpers ──
    def choose_source(self):
        path = self.choose_pdf(self.file_var)
        if not path:
            return
        try:
            pypdf = need("pypdf")
            self.page_count = len(pypdf.PdfReader(path).pages)
            self.info_var.set(f"{Path(path).name} — {self.page_count} page(s)")
        except Exception as exc:
            self.page_count = 0
            self.info_var.set(f"Could not read the PDF: {str(exc)[:90]}")
        self._refresh_placement_preview()

    def _describe(self, entry: dict) -> tuple:
        scope = entry.get("scope", "Last page only")
        pages = entry.get("pages_text", "") if scope == "Selected pages" else scope
        placement = entry["position"] if entry.get("visible") else "Invisible"
        return (
            entry.get("signer_name") or Path(entry["path"]).stem,
            Path(entry["path"]).name,
            pages,
            placement,
        )

    def _refresh(self):
        self.tree.delete(*self.tree.get_children())
        for entry in self.certificates:
            self.tree.insert("", "end", values=self._describe(entry))
        self._refresh_placement_preview()

    def _refresh_placement_preview(self):
        """Instantly redraw where each signature will land — no cryptography,
        so this can run on every change without any noticeable delay."""
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            return
        previous = getattr(self, "_placement_temp", None)
        try:
            result = render_signature_placements(source, self.certificates)
        except Exception:
            return
        self._placement_temp = result["output"]
        try:
            self.preview.set_zoom(1.0)
        except Exception:
            pass
        self.preview.load(result["output"], page=0)
        self.status_var.set(
            f"{len(self.certificates)} certificate(s) configured — "
            "placement shown live. This is a position preview, not a real signature."
        )
        if previous and previous != result["output"]:
            try:
                Path(previous).unlink(missing_ok=True)
            except Exception:
                pass

    def add_certificate(self):
        if not self.page_count:
            messagebox.showwarning(
                APP_NAME, "Select the PDF to sign first.", parent=self
            )
            return
        dialog = CertificateEntryDialog(self, self.page_count)
        if dialog.result:
            self.certificates.append(dialog.result)
            self._refresh()

    def _selected_index(self) -> Optional[int]:
        selection = self.tree.selection()
        if not selection:
            return None
        return self.tree.index(selection[0])

    def edit_certificate(self):
        index = self._selected_index()
        if index is None:
            messagebox.showwarning(APP_NAME, "Select a certificate to edit.", parent=self)
            return
        dialog = CertificateEntryDialog(self, self.page_count, self.certificates[index])
        if dialog.result:
            self.certificates[index] = dialog.result
            self._refresh()

    def remove_certificate(self):
        index = self._selected_index()
        if index is None:
            return
        del self.certificates[index]
        self._refresh()

    def move(self, delta: int):
        index = self._selected_index()
        if index is None:
            return
        target = index + delta
        if 0 <= target < len(self.certificates):
            self.certificates[index], self.certificates[target] = (
                self.certificates[target], self.certificates[index]
            )
            self._refresh()
            children = self.tree.get_children()
            if children:
                self.tree.selection_set(children[target])

    def make_test_certificate(self):
        output = filedialog.asksaveasfilename(
            parent=self, title="Save test certificate", defaultextension=".p12",
            initialfile="test_signing_certificate.p12",
            filetypes=[("PKCS#12 certificate", "*.p12")],
        )
        if not output:
            return
        self.run_job(
            "Creating a test certificate…",
            lambda: generate_test_certificate(
                output, "Test Signer", "Test Organisation", "IN", "test1234", 365
            ),
            lambda _r: messagebox.showinfo(
                APP_NAME,
                f"Test certificate created.\n\n{output}\n\nPassword: test1234",
                parent=self,
            ),
        )

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a PDF to sign.", parent=self)
            return
        if not self.certificates:
            messagebox.showwarning(
                APP_NAME, "Add at least one signature certificate.", parent=self
            )
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save signed PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_signed.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        entries = [dict(entry) for entry in self.certificates]
        self.run_job(
            "Applying digital signatures…",
            lambda: sign_pdf_multi(source, output, entries, log=self.log),
            self._signed,
        )

    def _signed(self, result):
        self.preview.load(result["output"])
        lines = [
            f"  page {item['page']:>3}  {item['signer'] or item['certificate']}"
            f"  ({'visible' if item['visible'] else 'invisible'})"
            for item in result["signatures"][:14]
        ]
        if len(result["signatures"]) > 14:
            lines.append(f"  … and {len(result['signatures']) - 14} more")
        messagebox.showinfo(
            APP_NAME,
            f"Applied {result['count']} signature(s) from "
            f"{result['certificates']} certificate(s).\n\n"
            + "\n".join(lines)
            + f"\n\n{result['output']}",
            parent=self,
        )

    def verify(self):
        path = filedialog.askopenfilename(
            parent=self, title="Select a signed PDF",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not path:
            return
        self.run_job(
            "Verifying signatures…",
            lambda: verify_pdf_signatures(path),
            self._verified,
        )

    def _verified(self, result):
        signatures = result.get("signatures", [])
        if not signatures:
            messagebox.showinfo(
                APP_NAME, "No digital signatures were found in this PDF.", parent=self
            )
            return
        lines = []
        for index, item in enumerate(signatures, 1):
            lines.append(
                f"{index}. {item.get('field', '')}\n"
                f"   intact: {item.get('intact')}   valid: {item.get('valid')}   "
                f"trusted: {item.get('trusted')}"
            )
        messagebox.showinfo(
            APP_NAME,
            f"{len(signatures)} signature(s) found.\n\n" + "\n".join(lines[:10]),
            parent=self,
        )


class CropPage(BasePage):
    title = "Crop PDF"
    description = "Trim margins from selected pages by points or percentage."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.pages_var = tk.StringVar()
        self.unit_var = tk.StringVar(value="points")
        self.left_var = tk.DoubleVar(value=0)
        self.top_var = tk.DoubleVar(value=0)
        self.right_var = tk.DoubleVar(value=0)
        self.bottom_var = tk.DoubleVar(value=0)

        self.section("Source PDF")
        self.file_row(self.file_var, lambda: self.choose_pdf(self.file_var))

        self.section("Pages")
        ttk.Entry(self.controls, textvariable=self.pages_var).pack(fill="x")
        ttk.Label(
            self.controls, text="Blank = all pages. Example: 1-3,5,8-10",
            style="Help.TLabel"
        ).pack(anchor="w", pady=(4, 0))

        self.section("Margins to remove")
        unit_row = ttk.Frame(self.controls, style="Panel.TFrame")
        unit_row.pack(fill="x", pady=(0, 8))
        ttk.Label(unit_row, text="Unit", style="Panel.TLabel").pack(side="left", padx=(0, 8))
        ttk.Combobox(
            unit_row, textvariable=self.unit_var, values=("points", "percent"),
            state="readonly", width=12
        ).pack(side="left")

        grid = ttk.Frame(self.controls, style="Panel.TFrame")
        grid.pack(fill="x")
        for column in range(2):
            grid.columnconfigure(column, weight=1)
        specs = (
            ("Left", self.left_var, 0, 0), ("Top", self.top_var, 0, 1),
            ("Right", self.right_var, 1, 0), ("Bottom", self.bottom_var, 1, 1),
        )
        for label, variable, row, column in specs:
            padx = (0, 8) if column == 0 else (8, 0)
            ttk.Label(grid, text=label, style="Panel.TLabel").grid(
                row=row * 2, column=column, sticky="w", padx=padx, pady=(8, 3)
            )
            ttk.Spinbox(
                grid, from_=0, to=500, increment=5, textvariable=variable
            ).grid(row=row * 2 + 1, column=column, sticky="ew", padx=padx)

        ttk.Label(
            self.controls,
            text="Cropping hides content outside the crop box but does not delete it. "
                 "Use Redact to permanently remove sensitive content.",
            style="Help.TLabel", wraplength=500
        ).pack(anchor="w", pady=(12, 0))
        ttk.Button(
            self.controls, text="Crop and Save PDF", command=self.process,
            style="Primary.TButton"
        ).pack(fill="x", pady=(16, 0), ipady=4)

    def preview_source(self):
        return self.file_var.get().strip()

    def build_preview_job(self, temporary):
        margins = (float(self.left_var.get()), float(self.top_var.get()),
                   float(self.right_var.get()), float(self.bottom_var.get()))
        if not any(margins):
            raise FeatureError("Enter at least one crop margin to preview.")
        args = (self.preview_source(), temporary, self.pages_var.get()) + margins + (
            self.unit_var.get(),
        )
        return lambda: crop_pdf(*args)

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a source PDF.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save cropped PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_cropped.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        args = (
            source, output, self.pages_var.get(),
            float(self.left_var.get()), float(self.top_var.get()),
            float(self.right_var.get()), float(self.bottom_var.get()),
            self.unit_var.get(),
        )
        self.run_job("Cropping pages…", lambda: crop_pdf(*args), self._done)

    def _done(self, result):
        self.preview.load(result["output"])
        messagebox.showinfo(
            APP_NAME, f"Cropped {result['pages']} page(s).\n\n{result['output']}", parent=self
        )


class RotatePage(BasePage):
    title = "Rotate PDF"
    description = "Rotate selected pages clockwise or anticlockwise in one step."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.pages_var = tk.StringVar()
        self.angle_var = tk.StringVar(value="90° clockwise")

        self.section("Source PDF")
        self.file_row(self.file_var, lambda: self.choose_pdf(self.file_var))
        self.section("Pages")
        ttk.Entry(self.controls, textvariable=self.pages_var).pack(fill="x")
        ttk.Label(
            self.controls, text="Blank = all pages. Example: 1-3,5,8-10",
            style="Help.TLabel"
        ).pack(anchor="w", pady=(4, 0))
        self.section("Rotation")
        ttk.Combobox(
            self.controls, textvariable=self.angle_var, state="readonly",
            values=("90° clockwise", "180°", "90° anticlockwise"),
        ).pack(fill="x")
        ttk.Button(
            self.controls, text="Rotate and Save PDF", command=self.process,
            style="Primary.TButton"
        ).pack(fill="x", pady=(18, 0), ipady=4)

    def preview_source(self):
        return self.file_var.get().strip()

    def build_preview_job(self, temporary):
        degrees = {"90° clockwise": 90, "180°": 180,
                   "90° anticlockwise": 270}[self.angle_var.get()]
        source, pages = self.preview_source(), self.pages_var.get()
        return lambda: rotate_pdf_pages(source, temporary, pages, degrees)

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a source PDF.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save rotated PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_rotated.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        degrees = {"90° clockwise": 90, "180°": 180, "90° anticlockwise": 270}[self.angle_var.get()]
        pages = self.pages_var.get()
        self.run_job(
            "Rotating pages…",
            lambda: rotate_pdf_pages(source, output, pages, degrees),
            self._done,
        )

    def _done(self, result):
        self.preview.load(result["output"])
        messagebox.showinfo(
            APP_NAME, f"Rotated {result['pages']} page(s) by {result['degrees']}°.\n\n{result['output']}",
            parent=self,
        )


class ProtectPage(BasePage):
    title = "Protect PDF"
    description = "Encrypt a PDF with AES-256 and control printing, copying and editing."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.password_var = tk.StringVar()
        self.confirm_var = tk.StringVar()
        self.owner_var = tk.StringVar()
        self.print_var = tk.BooleanVar(value=True)
        self.copy_var = tk.BooleanVar(value=False)
        self.modify_var = tk.BooleanVar(value=False)
        self.annotate_var = tk.BooleanVar(value=False)

        self.section("Source PDF")
        self.file_row(self.file_var, lambda: self.choose_pdf(self.file_var))

        self.section("Password")
        ttk.Label(self.controls, text="Open password (required to view)", style="Panel.TLabel").pack(anchor="w", pady=(0, 3))
        ttk.Entry(self.controls, textvariable=self.password_var, show="●").pack(fill="x")
        ttk.Label(self.controls, text="Confirm password", style="Panel.TLabel").pack(anchor="w", pady=(8, 3))
        ttk.Entry(self.controls, textvariable=self.confirm_var, show="●").pack(fill="x")
        ttk.Label(self.controls, text="Owner password (optional — for changing permissions)", style="Panel.TLabel").pack(anchor="w", pady=(8, 3))
        ttk.Entry(self.controls, textvariable=self.owner_var, show="●").pack(fill="x")

        self.section("Permissions")
        for text, variable in (
            ("Allow printing", self.print_var),
            ("Allow copying text and images", self.copy_var),
            ("Allow editing content", self.modify_var),
            ("Allow annotations and form filling", self.annotate_var),
        ):
            ttk.Checkbutton(self.controls, text=text, variable=variable).pack(anchor="w", pady=2)

        warn = tk.Frame(self.controls, bg=COLORS["blue_050"], padx=13, pady=11)
        warn.pack(fill="x", pady=(14, 0))
        tk.Label(
            warn,
            text="Store the password safely. If it is lost, the document cannot be recovered "
                 "by this application or by Anthropic.",
            bg=COLORS["blue_050"], fg=COLORS["blue_800"], font=("Segoe UI", 9),
            justify="left", wraplength=480,
        ).pack(anchor="w")

        ttk.Button(
            self.controls, text="Encrypt and Save PDF", command=self.process,
            style="Primary.TButton"
        ).pack(fill="x", pady=(16, 0), ipady=4)

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a source PDF.", parent=self)
            return
        password = self.password_var.get()
        if not password:
            messagebox.showwarning(APP_NAME, "Enter an open password.", parent=self)
            return
        if password != self.confirm_var.get():
            messagebox.showwarning(APP_NAME, "The passwords do not match.", parent=self)
            return
        if len(password) < 4:
            messagebox.showwarning(APP_NAME, "Use a password of at least 4 characters.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save protected PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_protected.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        args = (
            source, output, password, self.owner_var.get(),
            bool(self.print_var.get()), bool(self.copy_var.get()),
            bool(self.modify_var.get()), bool(self.annotate_var.get()),
        )
        self.run_job("Encrypting PDF…", lambda: protect_pdf(*args), self._done)

    def _done(self, result):
        messagebox.showinfo(
            APP_NAME,
            f"PDF encrypted with {result['encryption']}.\n\n{result['output']}\n\n"
            "Keep the password safe — it cannot be recovered.",
            parent=self,
        )


class UnlockPage(BasePage):
    title = "Unlock PDF"
    description = "Remove password protection from a PDF you have the password for."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.password_var = tk.StringVar()

        self.section("Protected PDF")
        row = ttk.Frame(self.controls, style="Panel.TFrame")
        row.pack(fill="x")
        ttk.Entry(row, textvariable=self.file_var).pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Browse PDF", command=self.choose_locked).pack(side="left", padx=(8, 0))
        ttk.Button(
            row, text="👁 Preview", command=lambda: self.preview_path(self.file_var),
            style="Quiet.TButton",
        ).pack(side="left", padx=(6, 0))

        self.section("Password")
        ttk.Entry(self.controls, textvariable=self.password_var, show="●").pack(fill="x")
        self.status_label = ttk.Label(self.controls, text="", style="Help.TLabel")
        self.status_label.pack(anchor="w", pady=(6, 0))

        notice = tk.Frame(self.controls, bg=COLORS["blue_100"], padx=13, pady=11)
        notice.pack(fill="x", pady=(14, 0))
        tk.Label(
            notice,
            text="Legal notice: use this only on documents you own or are authorised to unlock. "
                 "This tool requires the correct password — it does not crack or bypass encryption.",
            bg=COLORS["blue_100"], fg=COLORS["blue_900"], font=("Segoe UI", 9),
            justify="left", wraplength=480,
        ).pack(anchor="w")

        ttk.Button(
            self.controls, text="Unlock and Save PDF", command=self.process,
            style="Primary.TButton"
        ).pack(fill="x", pady=(16, 0), ipady=4)

    def choose_locked(self):
        path = filedialog.askopenfilename(
            parent=self, title="Select protected PDF", filetypes=[("PDF files", "*.pdf")]
        )
        if not path:
            return
        self.file_var.set(path)
        try:
            pymupdf = get_pymupdf()
            doc = pymupdf.open(path)
            locked = doc.needs_pass
            doc.close()
            if locked:
                self.status_label.configure(
                    text="This PDF is password-protected. Enter the password below.",
                    foreground=COLORS["warning"],
                )
            else:
                self.status_label.configure(
                    text="ℹ This PDF is not protected — no unlocking is needed.",
                    foreground=COLORS["muted"],
                )
                self.preview.load(path)
        except Exception as exc:
            self.status_label.configure(text=str(exc)[:120], foreground=COLORS["danger"])

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a protected PDF.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save unlocked PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_unlocked.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        password = self.password_var.get()
        self.run_job(
            "Unlocking PDF…",
            lambda: unlock_pdf(source, output, password),
            self._done,
        )

    def _done(self, result):
        self.preview.load(result["output"])
        messagebox.showinfo(
            APP_NAME, f"Password removed.\n\nPages: {result['pages']}\n{result['output']}",
            parent=self,
        )


class RedactionCanvas(ttk.Frame):
    """Scrollable, zoomable PDF canvas used by the redaction workspace."""

    def __init__(self, master, owner: "RedactPage"):
        super().__init__(master, style="Panel.TFrame", padding=12)
        self.owner = owner
        self.photo = None
        self.scale = 1.0
        self.image_origin = (20.0, 20.0)
        self.page_size = (0.0, 0.0)
        self.drag_start: Optional[tuple[float, float]] = None
        self.drag_item: Optional[int] = None

        top = ttk.Frame(self, style="Panel.TFrame")
        top.pack(fill="x", pady=(0, 8))
        self.prev_button = owner.action_button(
            top, "◀  Previous Page", owner.previous_page, COLORS["violet"], compact=True
        )
        self.prev_button.pack(side="left")
        self.page_var = tk.StringVar(value="No PDF loaded")
        ttk.Label(top, textvariable=self.page_var, style="Panel.TLabel").pack(
            side="left", expand=True
        )
        self.next_button = owner.action_button(
            top, "Next Page  ▶", owner.next_page, COLORS["violet"], compact=True
        )
        self.next_button.pack(side="right")

        zoom_row = ttk.Frame(self, style="Panel.TFrame")
        zoom_row.pack(fill="x", pady=(0, 7))
        ttk.Label(zoom_row, text="🔎 Zoom", style="Help.TLabel").pack(side="left")
        ttk.Scale(
            zoom_row, from_=60, to=220, variable=owner.zoom_var,
            command=lambda _value: self.render()
        ).pack(side="left", fill="x", expand=True, padx=8)
        self.zoom_label = ttk.Label(zoom_row, text="100%", style="Help.TLabel", width=6)
        self.zoom_label.pack(side="right")

        wrap = tk.Frame(
            self, bg=COLORS["blue_200"], bd=0,
            highlightthickness=2, highlightbackground=COLORS["blue_500"]
        )
        wrap.pack(fill="both", expand=True)
        self.canvas = tk.Canvas(
            wrap, bg="#DCE7F2", bd=0, highlightthickness=0,
            cursor="crosshair", xscrollincrement=10, yscrollincrement=10
        )
        vertical = ttk.Scrollbar(wrap, orient="vertical", command=self.canvas.yview)
        horizontal = ttk.Scrollbar(wrap, orient="horizontal", command=self.canvas.xview)
        self.canvas.configure(xscrollcommand=horizontal.set, yscrollcommand=vertical.set)
        vertical.pack(side="right", fill="y")
        horizontal.pack(side="bottom", fill="x")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.canvas.bind("<ButtonPress-1>", self._press)
        self.canvas.bind("<B1-Motion>", self._drag)
        self.canvas.bind("<ButtonRelease-1>", self._release)

        ttk.Label(
            self,
            text="🖱 Drag over sensitive content. Black = pending redaction; red = search result; purple = smart candidate.",
            style="Help.TLabel", wraplength=680, justify="left"
        ).pack(anchor="w", pady=(7, 0))
        self.blank()

    def blank(self, text: str = "📂 Open a PDF to begin redacting"):
        self.photo = None
        self.canvas.delete("all")
        self.canvas.configure(scrollregion=(0, 0, 700, 560))
        self.canvas.create_text(
            350, 260, text=text, fill=COLORS["muted"],
            font=("Segoe UI", 14), width=480, justify="center"
        )
        self.page_var.set("No PDF loaded")
        self.prev_button.configure(state="disabled")
        self.next_button.configure(state="disabled")

    def load(self):
        self.canvas.xview_moveto(0)
        self.canvas.yview_moveto(0)
        self.render()

    def render(self):
        source = self.owner.source_path
        if not source or not Path(source).is_file() or not self.owner.page_count:
            self.blank()
            return
        try:
            pymupdf = get_pymupdf()
            need("PIL", "pillow")
            from PIL import Image, ImageTk

            self.scale = max(0.6, min(2.2, float(self.owner.zoom_var.get()) / 100.0))
            self.zoom_label.configure(text=f"{round(self.scale * 100):d}%")
            doc = pymupdf.open(source)
            page = doc[self.owner.page_index]
            self.page_size = (float(page.rect.width), float(page.rect.height))
            pix = page.get_pixmap(matrix=pymupdf.Matrix(self.scale, self.scale), alpha=False)
            image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
            doc.close()
            self.photo = ImageTk.PhotoImage(image)
            ox, oy = self.image_origin
            self.canvas.delete("all")
            self.canvas.create_rectangle(
                ox - 4, oy - 4, ox + image.width + 4, oy + image.height + 4,
                fill="#9DB3C8", outline=""
            )
            self.canvas.create_image(ox, oy, image=self.photo, anchor="nw")
            self.canvas.configure(scrollregion=(0, 0, ox + image.width + 25, oy + image.height + 25))
            self.draw_overlays()
            self.page_var.set(
                f"Page {self.owner.page_index + 1} of {self.owner.page_count}  ·  "
                f"{len(self.owner.regions.get(self.owner.page_index, []))} pending"
            )
            self.prev_button.configure(state="normal" if self.owner.page_index else "disabled")
            self.next_button.configure(
                state="normal" if self.owner.page_index + 1 < self.owner.page_count else "disabled"
            )
        except Exception as exc:
            self.blank(f"Preview unavailable\n{exc}")

    def _canvas_rect(self, rect: tuple[float, float, float, float]) -> tuple[float, ...]:
        ox, oy = self.image_origin
        x0, y0, x1, y1 = rect
        return (
            ox + x0 * self.scale, oy + y0 * self.scale,
            ox + x1 * self.scale, oy + y1 * self.scale,
        )

    def draw_overlays(self):
        page_index = self.owner.page_index
        for region in self.owner.regions.get(page_index, []):
            self.canvas.create_rectangle(
                *self._canvas_rect(region.rect), fill="black", outline="black", width=1,
                tags=("redaction",)
            )
        for finding in self.owner.search_hits:
            if finding.page_index == page_index:
                self.canvas.create_rectangle(
                    *self._canvas_rect(finding.rect), outline=COLORS["red"], width=3,
                    tags=("search_hit",)
                )
        for finding in self.owner.preview_candidates():
            if finding.page_index == page_index:
                self.canvas.create_rectangle(
                    *self._canvas_rect(finding.rect), outline=COLORS["violet"],
                    width=2, dash=(6, 3), tags=("smart_hit",)
                )

    def _point(self, event) -> tuple[float, float]:
        return self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)

    def _inside_page(self, point: tuple[float, float]) -> bool:
        ox, oy = self.image_origin
        width, height = self.page_size
        return ox <= point[0] <= ox + width * self.scale and oy <= point[1] <= oy + height * self.scale

    def _clamp(self, point: tuple[float, float]) -> tuple[float, float]:
        ox, oy = self.image_origin
        width, height = self.page_size
        return (
            min(max(point[0], ox), ox + width * self.scale),
            min(max(point[1], oy), oy + height * self.scale),
        )

    def _press(self, event):
        if not self.owner.source_path or self.owner.busy:
            if not self.owner.source_path:
                self.owner.warn_load_pdf()
            return
        point = self._point(event)
        if not self._inside_page(point):
            return
        self.drag_start = point
        self.drag_item = self.canvas.create_rectangle(
            point[0], point[1], point[0], point[1], fill="black", outline="black"
        )

    def _drag(self, event):
        if self.drag_start is None or self.drag_item is None:
            return
        current = self._clamp(self._point(event))
        self.canvas.coords(self.drag_item, *self.drag_start, *current)

    def _release(self, event):
        if self.drag_start is None:
            return
        current = self._clamp(self._point(event))
        start = self.drag_start
        self.drag_start = None
        if self.drag_item is not None:
            self.canvas.delete(self.drag_item)
            self.drag_item = None
        ox, oy = self.image_origin
        x0, x1 = sorted(((start[0] - ox) / self.scale, (current[0] - ox) / self.scale))
        y0, y1 = sorted(((start[1] - oy) / self.scale, (current[1] - oy) / self.scale))
        brush = max(1.0, float(self.owner.brush_var.get()))
        if x1 - x0 < 2 and y1 - y0 < 2:
            x1, y1 = x0 + brush * 4, y0 + brush
        padding = brush / 2.0
        width, height = self.page_size
        rect = (
            max(0.0, x0 - padding), max(0.0, y0 - padding),
            min(width, x1 + padding), min(height, y1 + padding),
        )
        if rect[2] - rect[0] >= 1 and rect[3] - rect[1] >= 1:
            self.owner.add_region(RedactionRegion(
                self.owner.page_index, rect, "manual", "Drawn area", "Manual"
            ))


class RedactPage(ttk.Frame):
    """Full manual and smart redaction editor."""

    title = "PDF Redaction Studio"

    def __init__(self, master, app):
        super().__init__(master, style="App.TFrame", padding=(18, 14))
        self.app = app
        self.source_path: Optional[str] = None
        self.page_count = 0
        self.page_index = 0
        self.busy = False
        self.regions: dict[int, list[RedactionRegion]] = {}
        self.search_hits: list[SensitiveFinding] = []
        self.findings: list[SensitiveFinding] = []
        self.finding_by_id: dict[str, SensitiveFinding] = {}
        self.finding_keys: set[tuple] = set()
        self.applied_ids: set[str] = set()
        self.brush_var = tk.DoubleVar(value=4.0)
        self.zoom_var = tk.DoubleVar(value=100.0)
        self.search_var = tk.StringVar()
        self.source_var = tk.StringVar(value="No PDF selected")
        self.match_var = tk.StringVar(value="Searchable-text matches will appear in red.")
        self.status_var = tk.StringVar(value="Ready — all processing stays on this computer")

        self._build_header()
        self._build_workspace()
        self._build_statusbar()

    @staticmethod
    def action_button(master, text: str, command: Callable, color: str,
                      compact: bool = False) -> tk.Button:
        return tk.Button(
            master, text=text, command=command, bg=color, fg="white",
            activebackground=color, activeforeground="white", bd=0, relief="flat",
            highlightthickness=0, padx=10 if compact else 15,
            pady=6 if compact else 9, font=("Segoe UI", 9 if compact else 10, "bold"),
            cursor="hand2"
        )

    def _build_header(self):
        header = tk.Frame(
            self, bg=COLORS["white"], padx=16, pady=12,
            highlightthickness=1, highlightbackground=COLORS["blue_200"]
        )
        header.pack(fill="x", pady=(0, 10))
        title_area = tk.Frame(header, bg=COLORS["white"])
        title_area.pack(side="left", fill="x", expand=True)
        tk.Label(
            title_area, text="🛡️  PDF Redaction Studio", bg=COLORS["white"],
            fg=COLORS["blue_900"], font=("Segoe UI Semilight", 19), anchor="w"
        ).pack(anchor="w")
        tk.Label(
            title_area,
            text="Draw, detect, review and permanently remove sensitive information.",
            bg=COLORS["white"], fg=COLORS["muted"], font=("Segoe UI", 9)
        ).pack(anchor="w", pady=(2, 0))
        buttons = tk.Frame(header, bg=COLORS["white"])
        buttons.pack(side="right")
        self.action_button(
            buttons, "📂  Open PDF", self.open_pdf, COLORS["blue_700"]
        ).pack(side="left", padx=(0, 8))
        self.action_button(
            buttons, "💾  Save PDF", self.save_pdf, COLORS["green"]
        ).pack(side="left")

    def _build_workspace(self):
        source_card = tk.Frame(
            self, bg=COLORS["blue_050"], padx=12, pady=8,
            highlightthickness=1, highlightbackground=COLORS["blue_300"]
        )
        source_card.pack(fill="x", pady=(0, 9))
        tk.Label(
            source_card, text="📄", bg=COLORS["blue_050"], fg=COLORS["blue_700"],
            font=("Segoe UI Emoji", 12)
        ).pack(side="left")
        tk.Label(
            source_card, textvariable=self.source_var, bg=COLORS["blue_050"],
            fg=COLORS["ink"], font=("Segoe UI", 9), anchor="w"
        ).pack(side="left", fill="x", expand=True, padx=8)

        body = ttk.Panedwindow(self, orient="horizontal")
        body.pack(fill="both", expand=True)
        left = ttk.Frame(body, style="Panel.TFrame", padding=10)
        self.preview = RedactionCanvas(body, self)
        body.add(left, weight=2)
        body.add(self.preview, weight=3)

        self.notebook = ttk.Notebook(left)
        self.notebook.pack(fill="both", expand=True)
        self.manual_tab = ttk.Frame(self.notebook, style="Panel.TFrame", padding=12)
        self.smart_tab = ttk.Frame(self.notebook, style="Panel.TFrame", padding=10)
        self.notebook.add(self.manual_tab, text="✍  MANUAL REDACTION")
        self.notebook.add(self.smart_tab, text="🔍  SMART REDACTION")
        self.notebook.bind("<<NotebookTabChanged>>", lambda _event: self.preview.render())
        self._build_manual_tab()
        self._build_smart_tab()

    def _build_manual_tab(self):
        self._section_label(self.manual_tab, "Find text in the document")
        search_row = ttk.Frame(self.manual_tab, style="Panel.TFrame")
        search_row.pack(fill="x")
        ttk.Entry(search_row, textvariable=self.search_var).pack(
            side="left", fill="x", expand=True
        )
        self.action_button(
            search_row, "🔎 Find", self.search_document, COLORS["blue_700"], compact=True
        ).pack(side="left", padx=(7, 0))
        ttk.Label(
            self.manual_tab, textvariable=self.match_var, style="Help.TLabel",
            wraplength=430, justify="left"
        ).pack(anchor="w", pady=(5, 9))
        self.action_button(
            self.manual_tab, "🟧  Redact All Found Words", self.redact_search_hits,
            COLORS["orange"]
        ).pack(fill="x", pady=(0, 12))

        self._section_label(self.manual_tab, "Drawing controls")
        brush_card = tk.Frame(
            self.manual_tab, bg="#F5F3FF", padx=10, pady=10,
            highlightthickness=1, highlightbackground="#C4B5FD"
        )
        brush_card.pack(fill="x")
        tk.Label(
            brush_card, text="🖌️ Brush padding", bg="#F5F3FF", fg=COLORS["violet_dark"],
            font=("Segoe UI", 9, "bold")
        ).pack(anchor="w")
        scale_row = tk.Frame(brush_card, bg="#F5F3FF")
        scale_row.pack(fill="x", pady=(5, 0))
        ttk.Scale(
            scale_row, from_=1, to=30, variable=self.brush_var,
            command=lambda value: self.brush_label.configure(text=f"{float(value):.0f} pt")
        ).pack(side="left", fill="x", expand=True)
        self.brush_label = tk.Label(
            scale_row, text="4 pt", bg="#F5F3FF", fg=COLORS["violet_dark"],
            font=("Segoe UI", 9), width=6
        )
        self.brush_label.pack(side="right", padx=(8, 0))
        tk.Label(
            brush_card,
            text="Drag to make a rectangular box. Padding expands its edges to cover characters fully.",
            bg="#F5F3FF", fg=COLORS["muted"], font=("Segoe UI", 8),
            wraplength=420, justify="left"
        ).pack(anchor="w", pady=(5, 0))

        actions = ttk.Frame(self.manual_tab, style="Panel.TFrame")
        actions.pack(fill="x", pady=(12, 0))
        self.action_button(
            actions, "🗑  Clear Page", self.clear_current_page, COLORS["red"], compact=True
        ).pack(side="left", fill="x", expand=True, padx=(0, 5))
        self.action_button(
            actions, "🧹 Clear Search", self.clear_search, COLORS["violet"], compact=True
        ).pack(side="left", fill="x", expand=True, padx=(5, 0))

        warning = tk.Frame(
            self.manual_tab, bg="#FFF7ED", padx=11, pady=10,
            highlightthickness=1, highlightbackground="#FDBA74"
        )
        warning.pack(fill="x", pady=(14, 0))
        tk.Label(
            warning,
            text="⚠️ Saving applies true redaction: covered text and image pixels are removed from the new PDF. Keep the original file as your master copy.",
            bg="#FFF7ED", fg="#9A3412", font=("Segoe UI", 9),
            wraplength=420, justify="left"
        ).pack(anchor="w")

    def _build_smart_tab(self):
        top = ttk.Frame(self.smart_tab, style="Panel.TFrame")
        top.pack(fill="x")
        self.action_button(
            top, "🔍  Analyze Document", self.analyze_document, COLORS["blue_700"]
        ).pack(side="left")
        self.smart_count_var = tk.StringVar(value="No analysis yet")
        ttk.Label(top, textvariable=self.smart_count_var, style="Help.TLabel").pack(
            side="left", padx=(10, 0)
        )

        table_frame = tk.Frame(
            self.smart_tab, bg=COLORS["white"],
            highlightthickness=1, highlightbackground=COLORS["blue_300"]
        )
        table_frame.pack(fill="both", expand=True, pady=(9, 7))
        columns = ("selected", "category", "page", "value")
        self.finding_tree = ttk.Treeview(
            table_frame, columns=columns, show="headings", height=11,
            selectmode="browse", style="Redact.Treeview"
        )
        self.finding_tree.heading("selected", text="✓")
        self.finding_tree.heading("category", text="Category")
        self.finding_tree.heading("page", text="Page")
        self.finding_tree.heading("value", text="Detected value")
        self.finding_tree.column("selected", width=34, anchor="center", stretch=False)
        self.finding_tree.column("category", width=132, anchor="w")
        self.finding_tree.column("page", width=42, anchor="center", stretch=False)
        self.finding_tree.column("value", width=200, anchor="w")
        tree_scroll = ttk.Scrollbar(table_frame, orient="vertical", command=self.finding_tree.yview)
        self.finding_tree.configure(yscrollcommand=tree_scroll.set)
        tree_scroll.pack(side="right", fill="y")
        self.finding_tree.pack(side="left", fill="both", expand=True)
        self.finding_tree.tag_configure("applied", background="#DCFCE7")
        self.finding_tree.tag_configure("heuristic", foreground=COLORS["violet_dark"])
        self.finding_tree.bind("<Button-1>", self._tree_click)
        self.finding_tree.bind("<<TreeviewSelect>>", self._tree_selected)

        selection_row = ttk.Frame(self.smart_tab, style="Panel.TFrame")
        selection_row.pack(fill="x")
        self.action_button(
            selection_row, "☑ Select All", lambda: self.select_all_findings(True),
            COLORS["violet"], compact=True
        ).pack(side="left")
        self.action_button(
            selection_row, "☐ Deselect All", lambda: self.select_all_findings(False),
            COLORS["violet"], compact=True
        ).pack(side="left", padx=6)
        self.action_button(
            selection_row, "✅ Apply Selected", self.apply_selected_findings,
            COLORS["green"], compact=True
        ).pack(side="right")

        self._section_label(self.smart_tab, "Custom words or codes")
        self.custom_box = tk.Text(
            self.smart_tab, height=3, bg=COLORS["blue_050"], fg=COLORS["ink"],
            bd=0, highlightthickness=1, highlightbackground=COLORS["blue_300"],
            font=("Segoe UI", 9), wrap="word", padx=7, pady=5
        )
        self.custom_box.pack(fill="x")
        ttk.Label(
            self.smart_tab, text="Comma-separated or one item per line — e.g. Sohan, Mohan, 112233E",
            style="Help.TLabel"
        ).pack(anchor="w", pady=(3, 6))
        custom_actions = ttk.Frame(self.smart_tab, style="Panel.TFrame")
        custom_actions.pack(fill="x")
        self.action_button(
            custom_actions, "➕ Find & Add", self.find_custom_words,
            COLORS["blue_700"], compact=True
        ).pack(side="left")
        self.action_button(
            custom_actions, "🟧 Redact All", self.redact_all_custom_words,
            COLORS["orange"], compact=True
        ).pack(side="left", padx=6)
        self.action_button(
            custom_actions, "🗑 Clear", lambda: self.custom_box.delete("1.0", "end"),
            COLORS["red"], compact=True
        ).pack(side="right")

    @staticmethod
    def _section_label(master, text: str):
        ttk.Label(master, text=text.upper(), style="Eyebrow.TLabel").pack(
            anchor="w", pady=(10, 5)
        )

    def _build_statusbar(self):
        footer = ttk.Frame(self, style="App.TFrame")
        footer.pack(fill="x", pady=(9, 0))
        self.progress = ttk.Progressbar(footer, mode="indeterminate", length=220)
        self.progress.pack(side="left")
        ttk.Label(footer, textvariable=self.status_var, style="Status.TLabel").pack(
            side="left", padx=10
        )

    def warn_load_pdf(self):
        messagebox.showwarning(APP_NAME, "Please open a PDF file first.", parent=self)

    def open_pdf(self):
        if any(self.regions.values()) and not messagebox.askyesno(
            APP_NAME,
            "Opening another PDF will clear all unsaved redaction boxes. Continue?",
            parent=self,
        ):
            return
        path = filedialog.askopenfilename(
            parent=self, title="Open PDF for redaction", filetypes=[("PDF files", "*.pdf")]
        )
        if not path:
            return
        try:
            check_size(path)
            pymupdf = get_pymupdf()
            doc = pymupdf.open(path)
            if doc.needs_pass:
                doc.close()
                raise FeatureError("This PDF is password-protected. Use Unlock PDF first.")
            page_count = doc.page_count
            doc.close()
            if not page_count:
                raise FeatureError("The selected PDF has no pages.")
        except Exception as exc:
            messagebox.showerror(APP_NAME, f"Could not open this PDF.\n\n{exc}", parent=self)
            return
        self.source_path = path
        self.page_count = page_count
        self.page_index = 0
        self.source_var.set(f"{Path(path).name}   ·   {page_count} page(s)")
        self.regions.clear()
        self.search_hits.clear()
        self._clear_findings()
        self.match_var.set("Searchable-text matches will appear in red.")
        self.status_var.set(f"Loaded {Path(path).name}")
        self.preview.load()

    def set_page(self, index: int):
        if not self.page_count:
            self.warn_load_pdf()
            return
        self.page_index = max(0, min(index, self.page_count - 1))
        self.preview.load()

    def previous_page(self):
        if self.page_index > 0:
            self.set_page(self.page_index - 1)

    def next_page(self):
        if self.page_index + 1 < self.page_count:
            self.set_page(self.page_index + 1)

    @staticmethod
    def _region_key(page_index: int, rect: tuple[float, float, float, float]) -> tuple:
        return (page_index, *(round(value, 1) for value in rect))

    def add_region(self, region: RedactionRegion) -> bool:
        page_regions = self.regions.setdefault(region.page_index, [])
        key = self._region_key(region.page_index, region.rect)
        if any(self._region_key(item.page_index, item.rect) == key for item in page_regions):
            return False
        page_regions.append(region)
        self.status_var.set(
            f"Added {region.category} redaction on page {region.page_index + 1}"
        )
        self.preview.render()
        return True

    def clear_current_page(self):
        if not self.source_path:
            self.warn_load_pdf()
            return
        count = len(self.regions.get(self.page_index, []))
        if not count:
            messagebox.showinfo(APP_NAME, "There are no pending redactions on this page.", parent=self)
            return
        if not messagebox.askyesno(
            APP_NAME, f"Remove all {count} pending redaction(s) from this page?", parent=self
        ):
            return
        self.regions.pop(self.page_index, None)
        for finding in self.findings:
            if finding.page_index == self.page_index:
                self.applied_ids.discard(finding.finding_id)
                self._refresh_finding_row(finding)
        self.preview.render()
        self.status_var.set(f"Cleared pending redactions from page {self.page_index + 1}")

    def clear_search(self):
        self.search_hits.clear()
        self.match_var.set("Search highlights cleared.")
        self.preview.render()

    def _require_source(self) -> bool:
        if not self.source_path or not Path(self.source_path).is_file():
            self.warn_load_pdf()
            return False
        return True

    def _run_job(self, message: str, work: Callable[[], object],
                 done: Callable[[object], None], determinate: bool = False):
        if self.busy:
            messagebox.showinfo(APP_NAME, "Please wait for the current operation to finish.", parent=self)
            return
        self.busy = True
        self.status_var.set(message)
        if determinate:
            self.progress.stop()
            self.progress.configure(
                mode="determinate", maximum=max(1, self.page_count), value=0
            )
        else:
            self.progress.configure(mode="indeterminate")
            self.progress.start(12)

        def runner():
            try:
                result = work()
            except Exception as exc:
                detail = str(exc).strip() or exc.__class__.__name__
                if not isinstance(exc, FeatureError):
                    traceback.print_exc()
                self.after(0, lambda d=detail: self._job_failed(d))
            else:
                self.after(0, lambda r=result: self._job_done(r, done))

        threading.Thread(target=runner, daemon=True).start()

    def _job_failed(self, detail: str):
        self.busy = False
        self.progress.stop()
        self.progress.configure(mode="indeterminate", value=0)
        self.status_var.set("Operation failed")
        messagebox.showerror(APP_NAME, detail, parent=self)

    def _job_done(self, result: object, done: Callable[[object], None]):
        self.busy = False
        self.progress.stop()
        self.progress.configure(mode="indeterminate", value=0)
        done(result)

    def _analysis_progress(self, current: int, total: int):
        self.after(0, lambda: self._set_analysis_progress(current, total))

    def _set_analysis_progress(self, current: int, total: int):
        self.progress.configure(maximum=max(1, total), value=current)
        self.status_var.set(f"Analyzing page {current} of {total}…")

    def search_document(self):
        if not self._require_source():
            return
        term = self.search_var.get().strip()
        if not term:
            messagebox.showwarning(APP_NAME, "Type a word or phrase to find.", parent=self)
            return
        source = str(self.source_path)
        self._run_job(
            f"Searching for “{term}”…",
            lambda: find_pdf_occurrences(source, [term], "Search Match"),
            self._search_done,
        )

    def _search_done(self, result: object):
        findings = list(result)  # type: ignore[arg-type]
        self.search_hits = findings
        if not findings:
            self.match_var.set("No matches found.")
            self.status_var.set("No searchable-text matches found")
            self.preview.render()
            messagebox.showinfo(
                APP_NAME,
                "No matches were found. If this is a scanned PDF, run OCR PDF first.",
                parent=self,
            )
            return
        pages = sorted({item.page_index + 1 for item in findings})
        page_text = ", ".join(str(page) for page in pages[:12])
        self.match_var.set(f"{len(findings)} match(es) on page(s) {page_text}. Red boxes are previews.")
        self.status_var.set(f"Found {len(findings)} match(es)")
        self.page_index = findings[0].page_index
        self.preview.load()

    def redact_search_hits(self):
        if not self._require_source():
            return
        if not self.search_hits:
            messagebox.showwarning(APP_NAME, "Search for a word or phrase first.", parent=self)
            return
        added = 0
        for finding in self.search_hits:
            region = RedactionRegion(
                finding.page_index, finding.rect, "search", finding.value, "Search Match"
            )
            page_regions = self.regions.setdefault(region.page_index, [])
            key = self._region_key(region.page_index, region.rect)
            if not any(self._region_key(item.page_index, item.rect) == key for item in page_regions):
                page_regions.append(region)
                added += 1
        self.search_hits.clear()
        self.match_var.set(f"Added {added} found occurrence(s) to pending redactions.")
        self.status_var.set(f"Added {added} search redaction(s)")
        self.preview.render()

    def analyze_document(self):
        if not self._require_source():
            return
        source = str(self.source_path)
        self._run_job(
            "Analyzing document for sensitive information…",
            lambda: analyze_sensitive_pdf(source, self._analysis_progress),
            self._analysis_done,
            determinate=True,
        )

    def _analysis_done(self, result: object):
        findings = list(result)  # type: ignore[arg-type]
        self._add_findings(findings)
        self.smart_count_var.set(f"{len(self.findings)} item(s) in review list")
        self.status_var.set(f"Analysis complete — {len(findings)} new item(s) found")
        self.preview.render()
        if not findings:
            messagebox.showinfo(
                APP_NAME,
                "No sensitive patterns were detected. Scanned PDFs must be processed with OCR first.",
                parent=self,
            )

    def _finding_key(self, finding: SensitiveFinding) -> tuple:
        return (
            finding.page_index, finding.category.casefold(),
            *(round(value, 1) for value in finding.rect)
        )

    def _add_findings(self, findings: Sequence[SensitiveFinding]):
        for finding in findings:
            key = self._finding_key(finding)
            if key in self.finding_keys:
                continue
            self.finding_keys.add(key)
            self.findings.append(finding)
            self.finding_by_id[finding.finding_id] = finding
            self.finding_tree.insert(
                "", "end", iid=finding.finding_id,
                values=("☑" if finding.selected else "☐", finding.category,
                        finding.page_index + 1, finding.value),
                tags=("heuristic",) if finding.category.startswith("Possible") else ()
            )
        self.smart_count_var.set(f"{len(self.findings)} item(s) in review list")

    def _clear_findings(self):
        self.findings.clear()
        self.finding_by_id.clear()
        self.finding_keys.clear()
        self.applied_ids.clear()
        if hasattr(self, "finding_tree"):
            self.finding_tree.delete(*self.finding_tree.get_children())
        if hasattr(self, "smart_count_var"):
            self.smart_count_var.set("No analysis yet")

    def _refresh_finding_row(self, finding: SensitiveFinding):
        if not self.finding_tree.exists(finding.finding_id):
            return
        tags: tuple[str, ...]
        if finding.finding_id in self.applied_ids:
            tags = ("applied",)
        elif finding.category.startswith("Possible"):
            tags = ("heuristic",)
        else:
            tags = ()
        self.finding_tree.item(
            finding.finding_id,
            values=("☑" if finding.selected else "☐", finding.category,
                    finding.page_index + 1, finding.value),
            tags=tags,
        )

    def _tree_click(self, event):
        row = self.finding_tree.identify_row(event.y)
        column = self.finding_tree.identify_column(event.x)
        if not row:
            return
        self.finding_tree.selection_set(row)
        if column == "#1":
            finding = self.finding_by_id.get(row)
            if finding:
                finding.selected = not finding.selected
                self._refresh_finding_row(finding)
                self.preview.render()
            return "break"
        return None

    def _tree_selected(self, _event=None):
        selected = self.finding_tree.selection()
        if not selected:
            return
        finding = self.finding_by_id.get(selected[0])
        if finding and self.page_count:
            self.page_index = finding.page_index
            self.preview.load()

    def select_all_findings(self, selected: bool):
        if not self.findings:
            messagebox.showwarning(APP_NAME, "Analyze the PDF or add custom words first.", parent=self)
            return
        for finding in self.findings:
            finding.selected = selected
            self._refresh_finding_row(finding)
        self.status_var.set("Selected all findings" if selected else "Deselected all findings")
        self.preview.render()

    def preview_candidates(self) -> list[SensitiveFinding]:
        return [
            finding for finding in self.findings
            if finding.selected and finding.finding_id not in self.applied_ids
        ]

    def apply_selected_findings(self):
        if not self._require_source():
            return
        selected = [item for item in self.findings if item.selected]
        if not selected:
            messagebox.showwarning(APP_NAME, "Select at least one item in the review list.", parent=self)
            return
        added = 0
        for finding in selected:
            region = RedactionRegion(
                finding.page_index, finding.rect, "smart", finding.value, finding.category
            )
            page_regions = self.regions.setdefault(region.page_index, [])
            key = self._region_key(region.page_index, region.rect)
            if not any(self._region_key(item.page_index, item.rect) == key for item in page_regions):
                page_regions.append(region)
                added += 1
            self.applied_ids.add(finding.finding_id)
            self._refresh_finding_row(finding)
        self.status_var.set(f"Applied {added} new smart redaction(s)")
        self.preview.render()
        messagebox.showinfo(
            APP_NAME,
            f"{added} new redaction box(es) applied. Review the black boxes, then click Save PDF.",
            parent=self,
        )

    def _custom_terms(self) -> list[str]:
        raw = self.custom_box.get("1.0", "end").strip()
        terms: list[str] = []
        seen: set[str] = set()
        for part in re.split(r"[,\n]+", raw):
            term = part.strip()
            if term and term.casefold() not in seen:
                seen.add(term.casefold())
                terms.append(term)
        return terms

    def find_custom_words(self):
        if not self._require_source():
            return
        terms = self._custom_terms()
        if not terms:
            messagebox.showwarning(APP_NAME, "Enter one or more custom words or codes.", parent=self)
            return
        source = str(self.source_path)
        self._run_job(
            "Finding custom words…",
            lambda: find_pdf_occurrences(source, terms, "Custom Word"),
            self._custom_found,
        )

    def _custom_found(self, result: object):
        findings = list(result)  # type: ignore[arg-type]
        before = len(self.findings)
        self._add_findings(findings)
        added = len(self.findings) - before
        self.status_var.set(f"Added {added} custom match(es) to the review list")
        self.preview.render()
        if not findings:
            messagebox.showinfo(
                APP_NAME, "No custom words were found. Scanned PDFs require OCR first.", parent=self
            )

    def redact_all_custom_words(self):
        if not self._require_source():
            return
        terms = self._custom_terms()
        if not terms:
            messagebox.showwarning(APP_NAME, "Enter one or more custom words or codes.", parent=self)
            return
        source = str(self.source_path)
        self._run_job(
            "Finding and redacting all custom words…",
            lambda: find_pdf_occurrences(source, terms, "Custom Word"),
            self._custom_redact_done,
        )

    def _custom_redact_done(self, result: object):
        findings = list(result)  # type: ignore[arg-type]
        if not findings:
            self.status_var.set("No custom-word matches found")
            messagebox.showinfo(
                APP_NAME, "No custom words were found. Scanned PDFs require OCR first.", parent=self
            )
            return
        added = 0
        for finding in findings:
            region = RedactionRegion(
                finding.page_index, finding.rect, "custom", finding.value, "Custom Word"
            )
            page_regions = self.regions.setdefault(region.page_index, [])
            key = self._region_key(region.page_index, region.rect)
            if not any(self._region_key(item.page_index, item.rect) == key for item in page_regions):
                page_regions.append(region)
                added += 1
        self.status_var.set(f"Added {added} custom-word redaction(s)")
        self.preview.render()
        messagebox.showinfo(
            APP_NAME, f"Added {added} custom-word redaction box(es). Review and save the PDF.",
            parent=self
        )

    def save_pdf(self):
        if not self._require_source():
            return
        areas = [
            (region.page_index, *region.rect)
            for page_index in sorted(self.regions)
            for region in self.regions[page_index]
        ]
        if not areas:
            messagebox.showwarning(
                APP_NAME, "Add at least one manual, search, smart or custom redaction first.",
                parent=self
            )
            return
        if not messagebox.askyesno(
            APP_NAME,
            f"Permanently apply {len(areas)} redaction box(es) to a new PDF?\n\n"
            "The covered content cannot be recovered from the saved output.",
            parent=self,
        ):
            return
        source = str(self.source_path)
        output = filedialog.asksaveasfilename(
            parent=self, title="Save permanently redacted PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_redacted.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        try:
            require_distinct_output(output, (source,))
        except FeatureError as exc:
            messagebox.showwarning(APP_NAME, str(exc), parent=self)
            return
        self._run_job(
            "Permanently applying redactions…",
            lambda: redact_pdf_areas(source, output, areas),
            self._save_done,
        )

    def _save_done(self, result: object):
        data = dict(result)  # type: ignore[arg-type]
        self.status_var.set(
            f"Saved {data['redacted']} permanent redaction(s) to {Path(data['output']).name}"
        )
        messagebox.showinfo(
            APP_NAME,
            f"✅ Redacted PDF saved successfully.\n\n"
            f"Permanent redactions: {data['redacted']}\n{data['output']}",
            parent=self,
        )


class PageNumbersPage(BasePage):
    title = "Add Page Numbers"
    description = "Stamp page numbers with custom position, starting number and format."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.position_var = tk.StringVar(value="Bottom centre")
        self.format_var = tk.StringVar(value="{n}")
        self.start_var = tk.IntVar(value=1)
        self.first_var = tk.IntVar(value=1)
        self.size_var = tk.IntVar(value=10)
        self.margin_var = tk.DoubleVar(value=28)

        self.section("Source PDF")
        self.file_row(self.file_var, lambda: self.choose_pdf(self.file_var))

        self.section("Placement")
        ttk.Combobox(
            self.controls, textvariable=self.position_var,
            values=tuple(PAGE_NUMBER_POSITIONS), state="readonly"
        ).pack(fill="x")

        self.section("Format")
        ttk.Combobox(
            self.controls, textvariable=self.format_var, state="normal",
            values=("{n}", "Page {n}", "{n} of {total}", "Page {n} of {total}", "- {n} -"),
        ).pack(fill="x")
        ttk.Label(
            self.controls,
            text="{n} = page number, {total} = total numbered pages. You may type a custom format.",
            style="Help.TLabel", wraplength=490,
        ).pack(anchor="w", pady=(4, 0))

        grid = ttk.Frame(self.controls, style="Panel.TFrame")
        grid.pack(fill="x", pady=(12, 0))
        for column in range(2):
            grid.columnconfigure(column, weight=1)
        specs = (
            ("Start numbering at", self.start_var, 1, 9999, 0, 0),
            ("First page to stamp", self.first_var, 1, 9999, 0, 1),
            ("Font size (points)", self.size_var, 6, 40, 1, 0),
            ("Margin from edge", self.margin_var, 5, 120, 1, 1),
        )
        for label, variable, low, high, row, column in specs:
            padx = (0, 8) if column == 0 else (8, 0)
            ttk.Label(grid, text=label, style="Panel.TLabel").grid(
                row=row * 2, column=column, sticky="w", padx=padx, pady=(8, 3)
            )
            ttk.Spinbox(
                grid, from_=low, to=high, increment=1, textvariable=variable
            ).grid(row=row * 2 + 1, column=column, sticky="ew", padx=padx)

        ttk.Button(
            self.controls, text="Add Page Numbers and Save", command=self.process,
            style="Primary.TButton"
        ).pack(fill="x", pady=(18, 0), ipady=4)

    def live_preview_vars(self) -> tuple:
        return (
            self.file_var, self.position_var, self.format_var,
            self.start_var, self.first_var, self.size_var, self.margin_var,
        )

    def preview_source(self):
        return self.file_var.get().strip()

    def build_preview_job(self, temporary):
        args = (
            self.preview_source(), temporary, self.position_var.get(),
            int(self.start_var.get()), int(self.first_var.get()),
            self.format_var.get(), int(self.size_var.get()),
            float(self.margin_var.get()),
        )
        return lambda: add_page_numbers(*args)

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a source PDF.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save numbered PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_numbered.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        args = (
            source, output, self.position_var.get(),
            int(self.start_var.get()), int(self.first_var.get()),
            self.format_var.get(), int(self.size_var.get()),
            float(self.margin_var.get()),
        )
        self.run_job("Adding page numbers…", lambda: add_page_numbers(*args), self._done)

    def _done(self, result):
        self.preview.load(result["output"])
        messagebox.showinfo(
            APP_NAME, f"Numbered {result['pages']} page(s).\n\n{result['output']}", parent=self
        )


class OcrPage(BasePage):
    title = "OCR PDF"
    description = "Make a scanned PDF searchable by adding an invisible text layer behind the page image."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.language_var = tk.StringVar(value="English")
        self.dpi_var = tk.IntVar(value=300)
        self.tesseract_var = tk.StringVar(value=find_tesseract_executable() or "")
        self.status_var = tk.StringVar()

        self.section("Scanned PDF")
        self.file_row(self.file_var, self.choose_and_check)
        self.scan_status = ttk.Label(self.controls, text="", style="Help.TLabel")
        self.scan_status.pack(anchor="w", pady=(6, 0))

        self.section("OCR language")
        ocr_names = tuple(
            name for name, code in LANGUAGES.items()
            if name != "Auto detect" and code in TESSERACT_LANGUAGES
        )
        ttk.Combobox(
            self.controls, textvariable=self.language_var,
            values=ocr_names, state="readonly"
        ).pack(fill="x")

        self.section("Quality")
        ttk.Combobox(
            self.controls, textvariable=self.dpi_var, state="readonly",
            values=(200, 300, 400),
        ).pack(fill="x")
        ttk.Label(
            self.controls,
            text="300 DPI suits most documents. 400 improves small print but is slower and larger.",
            style="Help.TLabel", wraplength=490,
        ).pack(anchor="w", pady=(4, 0))

        self.section("Tesseract engine")
        engine_row = ttk.Frame(self.controls, style="Panel.TFrame")
        engine_row.pack(fill="x")
        ttk.Entry(engine_row, textvariable=self.tesseract_var).pack(side="left", fill="x", expand=True)
        ttk.Button(
            engine_row, text="Locate Tesseract", command=self.browse_tesseract,
            style="Quiet.TButton"
        ).pack(side="left", padx=(8, 0))
        self.engine_label = ttk.Label(self.controls, textvariable=self.status_var, style="Help.TLabel")
        self.engine_label.pack(anchor="w", pady=(6, 0))
        self._refresh_status()

        ttk.Button(
            self.controls, text="Run OCR and Save Searchable PDF", command=self.process,
            style="Primary.TButton"
        ).pack(fill="x", pady=(18, 0), ipady=4)

    def choose_and_check(self):
        path = self.choose_pdf(self.file_var)
        if not path:
            return
        try:
            if pdf_needs_ocr(path):
                self.scan_status.configure(
                    text="✔ This looks like a scanned PDF — OCR will help.",
                    foreground=COLORS["success"],
                )
            else:
                self.scan_status.configure(
                    text="ℹ This PDF already has selectable text — OCR may not be needed.",
                    foreground=COLORS["muted"],
                )
        except Exception:
            self.scan_status.configure(text="", foreground=COLORS["muted"])

    def browse_tesseract(self):
        path = filedialog.askopenfilename(
            parent=self, title="Locate Tesseract OCR executable",
            filetypes=[("Tesseract executable", "tesseract.exe"), ("All files", "*.*")],
        )
        if path:
            self.tesseract_var.set(path)
            self._refresh_status()

    def _refresh_status(self):
        executable = find_tesseract_executable(self.tesseract_var.get().strip())
        if executable:
            self.tesseract_var.set(executable)
            installed = get_available_tesseract_langs(executable)
            if installed:
                names = [TESSERACT_LANG_NAMES.get(c, c) for c in installed]
                line = ", ".join(names[:8])
                if len(names) > 8:
                    line += f" (+{len(names) - 8} more)"
                self.status_var.set(f"✔ OCR ready  |  Packs: {line}")
                self.engine_label.configure(foreground=COLORS["success"])
            else:
                self.status_var.set("⚠ Tesseract found but no language packs installed.")
                self.engine_label.configure(foreground=COLORS["warning"])
        else:
            self.status_var.set("✗ Tesseract not found — install it to use OCR.")
            self.engine_label.configure(foreground=COLORS["danger"])

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a scanned PDF.", parent=self)
            return
        code = LANGUAGES.get(self.language_var.get(), "en")
        tess_code = TESSERACT_LANGUAGES.get(code, "eng")
        tesseract_path = self.tesseract_var.get().strip() or None
        installed = get_available_tesseract_langs(tesseract_path)
        if installed and tess_code not in installed:
            friendly = TESSERACT_LANG_NAMES.get(tess_code, tess_code)
            if not messagebox.askyesno(
                APP_NAME,
                f"The '{tess_code}' ({friendly}) language pack is not installed.\n\n"
                f"Installed: {', '.join(installed)}\n\n"
                f"Download it from:\n"
                f"https://github.com/tesseract-ocr/tessdata/raw/main/{tess_code}.traineddata\n\n"
                "Proceed anyway?",
                parent=self,
            ):
                return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save searchable PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_ocr.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        dpi = int(self.dpi_var.get())
        self.run_job(
            "Running OCR — this may take a while…",
            lambda: ocr_pdf_searchable(source, output, tess_code, dpi, tesseract_path),
            self._done,
        )

    def _done(self, result):
        self.preview.load(result["output"])
        messagebox.showinfo(
            APP_NAME,
            f"Searchable PDF created.\n\nPages: {result['pages']}\n"
            f"Language: {result['language']}\n\n{result['output']}",
            parent=self,
        )


class ScanPage(BasePage):
    title = "Scan to PDF"
    description = "Turn phone photos or scanner images into a clean, enhanced PDF."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.files: list[str] = []
        self.enhance_var = tk.BooleanVar(value=True)
        self.gray_var = tk.BooleanVar(value=False)
        self.deskew_var = tk.BooleanVar(value=True)
        self.quality_var = tk.IntVar(value=88)

        self.section("Scanned images")
        self.listbox = tk.Listbox(
            self.controls, height=11, bg=COLORS["blue_050"], fg=COLORS["ink"],
            selectbackground=COLORS["blue_700"], selectforeground=COLORS["white"], bd=0,
            highlightthickness=1, highlightbackground=COLORS["line"],
            font=("Segoe UI", 10), activestyle="none",
        )
        self.listbox.pack(fill="both", expand=True)
        buttons = ttk.Frame(self.controls, style="Panel.TFrame")
        buttons.pack(fill="x", pady=8)
        for text, command in (
            ("Add images", self.add_files), ("Remove", self.remove),
            ("Move up", lambda: self.move(-1)), ("Move down", lambda: self.move(1)),
            ("Clear", self.clear),
        ):
            ttk.Button(buttons, text=text, command=command, style="Quiet.TButton").pack(
                side="left", padx=(0, 5)
            )

        self.section("Enhancement")
        for text, variable in (
            ("Auto-enhance (contrast, sharpness) — recommended", self.enhance_var),
            ("Convert to grayscale (smaller file)", self.gray_var),
            ("Auto-rotate using EXIF orientation", self.deskew_var),
        ):
            ttk.Checkbutton(self.controls, text=text, variable=variable).pack(anchor="w", pady=2)

        quality_row = ttk.Frame(self.controls, style="Panel.TFrame")
        quality_row.pack(fill="x", pady=(10, 0))
        ttk.Label(quality_row, text="JPEG quality", style="Panel.TLabel").pack(side="left", padx=(0, 8))
        ttk.Spinbox(
            quality_row, from_=50, to=100, increment=2,
            textvariable=self.quality_var, width=8
        ).pack(side="left")

        ttk.Label(
            self.controls,
            text="Tip: after creating the PDF, run OCR PDF to make the scanned text searchable.",
            style="Help.TLabel", wraplength=500,
        ).pack(anchor="w", pady=(12, 0))

        ttk.Button(
            self.controls, text="Create PDF from Scans", command=self.process,
            style="Primary.TButton"
        ).pack(fill="x", pady=(14, 0), ipady=4)

    def refresh(self, select: Optional[int] = None):
        self.listbox.delete(0, "end")
        for number, filename in enumerate(self.files, start=1):
            self.listbox.insert("end", f"{number:02d}.  {Path(filename).name}")
        if select is not None and self.files:
            select = max(0, min(select, len(self.files) - 1))
            self.listbox.selection_set(select)

    def add_files(self):
        paths = filedialog.askopenfilenames(
            parent=self, title="Select scanned images in page order",
            filetypes=[("Images", "*.png *.jpg *.jpeg *.tif *.tiff *.bmp *.webp")],
        )
        for path in paths:
            if path not in self.files:
                self.files.append(path)
        self.refresh(len(self.files) - 1 if self.files else None)

    def remove(self):
        selected = self.listbox.curselection()
        if selected:
            del self.files[selected[0]]
            self.refresh(min(selected[0], len(self.files) - 1) if self.files else None)

    def move(self, delta: int):
        selected = self.listbox.curselection()
        if not selected:
            return
        current = selected[0]
        target = current + delta
        if 0 <= target < len(self.files):
            self.files[current], self.files[target] = self.files[target], self.files[current]
            self.refresh(target)

    def clear(self):
        self.files.clear()
        self.refresh()
        self.preview.clear()

    def process(self):
        if not self.files:
            messagebox.showwarning(APP_NAME, "Add at least one scanned image.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save scanned PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(self.files[0]).stem)}_scan.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        args = (
            tuple(self.files), output, bool(self.enhance_var.get()),
            bool(self.gray_var.get()), bool(self.deskew_var.get()),
            int(self.quality_var.get()),
        )
        self.run_job("Building scanned PDF…", lambda: scan_to_pdf(*args), self._done)

    def _done(self, result):
        self.preview.load(result["output"])
        messagebox.showinfo(
            APP_NAME, f"Created a {result['pages']}-page PDF.\n\n{result['output']}", parent=self
        )


class ComparePage(BasePage):
    title = "Compare PDF"
    description = "Find text differences between two versions of a document."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_a = tk.StringVar()
        self.file_b = tk.StringVar()

        self.section("Original document (A)")
        row_a = ttk.Frame(self.controls, style="Panel.TFrame")
        row_a.pack(fill="x")
        ttk.Entry(row_a, textvariable=self.file_a).pack(side="left", fill="x", expand=True)
        ttk.Button(
            row_a, text="Browse", command=lambda: self.choose_pdf(self.file_a)
        ).pack(side="left", padx=(8, 0))
        ttk.Button(
            row_a, text="👁 Preview", command=lambda: self.preview_path(self.file_a),
            style="Quiet.TButton",
        ).pack(side="left", padx=(6, 0))

        self.section("Revised document (B)")
        row_b = ttk.Frame(self.controls, style="Panel.TFrame")
        row_b.pack(fill="x")
        ttk.Entry(row_b, textvariable=self.file_b).pack(side="left", fill="x", expand=True)
        ttk.Button(
            row_b, text="Browse", command=lambda: self.choose_pdf(self.file_b)
        ).pack(side="left", padx=(8, 0))
        ttk.Button(
            row_b, text="👁 Preview", command=lambda: self.preview_path(self.file_b),
            style="Quiet.TButton",
        ).pack(side="left", padx=(6, 0))

        self.section("Differences")
        self.report_box = tk.Text(
            self.controls, height=15, bg=COLORS["blue_050"], fg=COLORS["ink"], bd=0,
            highlightthickness=1, highlightbackground=COLORS["line"],
            font=("Consolas", 9), wrap="none", padx=8, pady=6,
        )
        self.report_box.pack(fill="both", expand=True)
        self.report_box.tag_configure("added", foreground=COLORS["blue_600"])
        self.report_box.tag_configure("removed", foreground=COLORS["blue_900"])
        self.report_box.tag_configure("removed", foreground=COLORS["blue_900"], font=("Consolas", 9, "bold"))
        self.report_box.tag_configure("head", foreground=COLORS["blue_500"], font=("Consolas", 9, "bold"))
        self.report_box.configure(state="disabled")

        action_row = ttk.Frame(self.controls, style="Panel.TFrame")
        action_row.pack(fill="x", pady=(12, 0))
        ttk.Button(
            action_row, text="Compare Documents", command=self.process,
            style="Primary.TButton"
        ).pack(side="left", fill="x", expand=True, ipady=4)
        ttk.Button(
            action_row, text="Save report", command=self.save_report,
            style="Quiet.TButton"
        ).pack(side="left", padx=(8, 0))
        self._last_report = ""

    def process(self):
        path_a, path_b = self.file_a.get().strip(), self.file_b.get().strip()
        if not Path(path_a).is_file() or not Path(path_b).is_file():
            messagebox.showwarning(APP_NAME, "Select both PDF files.", parent=self)
            return
        self.run_job("Comparing documents…", lambda: compare_pdfs(path_a, path_b), self._done)

    def _done(self, result):
        self._last_report = result["report"]
        self.report_box.configure(state="normal")
        self.report_box.delete("1.0", "end")
        for line in result["report"].splitlines():
            if line.startswith("  B+"):
                self.report_box.insert("end", line + "\n", "added")
            elif line.startswith("  A-"):
                self.report_box.insert("end", line + "\n", "removed")
            elif line.startswith("---") or line.startswith("FILE") or line.startswith("="):
                self.report_box.insert("end", line + "\n", "head")
            else:
                self.report_box.insert("end", line + "\n")
        self.report_box.configure(state="disabled")
        messagebox.showinfo(
            APP_NAME,
            f"Comparison complete.\n\n"
            f"Similarity: {result['similarity']}%\n"
            f"Changed pages: {len(result['changed_pages'])}\n"
            f"Lines added in B: {result['added']}\n"
            f"Lines removed from A: {result['removed']}",
            parent=self,
        )

    def save_report(self):
        if not self._last_report:
            messagebox.showwarning(APP_NAME, "Run a comparison first.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save comparison report", defaultextension=".txt",
            initialfile="pdf_comparison_report.txt",
            filetypes=[("Text files", "*.txt")],
        )
        if output:
            Path(output).write_text(self._last_report, encoding="utf-8")
            messagebox.showinfo(APP_NAME, f"Report saved.\n\n{output}", parent=self)


class RepairPage(BasePage):
    title = "Repair PDF"
    description = "Rebuild a damaged or corrupt PDF so it opens and prints correctly again."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()

        self.section("Damaged PDF")
        row = ttk.Frame(self.controls, style="Panel.TFrame")
        row.pack(fill="x")
        ttk.Entry(row, textvariable=self.file_var).pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Browse PDF", command=self.choose_any).pack(side="left", padx=(8, 0))

        self.section("Diagnosis")
        self.report_box = tk.Text(
            self.controls, height=12, bg=COLORS["blue_050"], fg=COLORS["ink"], bd=0,
            highlightthickness=1, highlightbackground=COLORS["line"],
            font=("Consolas", 9), wrap="word", padx=8, pady=6,
        )
        self.report_box.pack(fill="both", expand=True)
        self.report_box.insert("1.0", "Select a PDF to begin.")
        self.report_box.configure(state="disabled")

        ttk.Label(
            self.controls,
            text="Repair rebuilds the cross-reference table and sanitises content streams. "
                 "Severely damaged files may lose some content — always keep the original.",
            style="Help.TLabel", wraplength=500,
        ).pack(anchor="w", pady=(12, 0))

        ttk.Button(
            self.controls, text="Repair and Save PDF", command=self.process,
            style="Primary.TButton"
        ).pack(fill="x", pady=(14, 0), ipady=4)

    def choose_any(self):
        path = filedialog.askopenfilename(
            parent=self, title="Select damaged PDF",
            filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")],
        )
        if path:
            self.file_var.set(path)
            try:
                self.preview.load(path)
            except Exception:
                pass

    def _write(self, text: str):
        self.report_box.configure(state="normal")
        self.report_box.delete("1.0", "end")
        self.report_box.insert("1.0", text)
        self.report_box.configure(state="disabled")

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a PDF file.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save repaired PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_repaired.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        self.run_job("Repairing PDF…", lambda: repair_pdf(source, output), self._done)

    def _done(self, result):
        lines = [
            f"Pages found        : {result['pages']}",
            f"Pages readable     : {result['readable']}",
            f"Size before        : {human_size(result['before'])}",
            f"Size after         : {human_size(result['after'])}",
            "",
        ]
        if result["notes"]:
            lines.append("Issues detected:")
            lines.extend(f"  • {note}" for note in result["notes"])
        else:
            lines.append("No structural issues detected — file rebuilt cleanly.")
        self._write("\n".join(lines))
        self.preview.load(result["output"])
        messagebox.showinfo(
            APP_NAME,
            f"Repair complete.\n\nPages: {result['pages']} "
            f"({result['readable']} readable)\n\n{result['output']}",
            parent=self,
        )


class FormsPage(BasePage):
    title = "PDF Forms"
    description = "Read, fill and flatten interactive PDF form fields."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.fields: list[dict] = []
        self.entries: dict[str, tk.StringVar] = {}

        self.section("Form PDF")
        self.file_row(self.file_var, self.load_form)

        self.section("Fields")
        container = ttk.Frame(self.controls, style="Panel.TFrame")
        container.pack(fill="both", expand=True)
        self.canvas = tk.Canvas(
            container, bg=COLORS["panel"], bd=0, highlightthickness=1,
            highlightbackground=COLORS["line"], height=250,
        )
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=self.canvas.yview)
        self.field_frame = ttk.Frame(self.canvas, style="Panel.TFrame")
        self.field_frame.bind(
            "<Configure>",
            lambda _e: self.canvas.configure(scrollregion=self.canvas.bbox("all")),
        )
        self.canvas.create_window((0, 0), window=self.field_frame, anchor="nw")
        self.canvas.configure(yscrollcommand=scrollbar.set)
        self.canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        ttk.Label(
            self.field_frame, text="Load a PDF form to see its fields.",
            style="Help.TLabel"
        ).pack(anchor="w", padx=10, pady=10)

        buttons = ttk.Frame(self.controls, style="Panel.TFrame")
        buttons.pack(fill="x", pady=(12, 0))
        ttk.Button(
            buttons, text="Fill and Save", command=self.process, style="Primary.TButton"
        ).pack(side="left", fill="x", expand=True, ipady=4)
        ttk.Button(
            buttons, text="Flatten form", command=self.flatten, style="Quiet.TButton"
        ).pack(side="left", padx=(8, 0))
        ttk.Button(
            buttons, text="Export field list", command=self.export_fields, style="Quiet.TButton"
        ).pack(side="left", padx=(8, 0))

    def load_form(self):
        path = self.choose_pdf(self.file_var)
        if not path:
            return
        try:
            result = read_pdf_form_fields(path)
        except Exception as exc:
            messagebox.showerror(APP_NAME, str(exc), parent=self)
            return
        self.fields = result["fields"]
        for child in self.field_frame.winfo_children():
            child.destroy()
        self.entries.clear()
        if not self.fields:
            ttk.Label(
                self.field_frame,
                text="This PDF has no interactive form fields.\n\n"
                     "It may be a flat/scanned form — use Edit PDF to add text, "
                     "or OCR PDF first if it is scanned.",
                style="Help.TLabel", wraplength=430, justify="left",
            ).pack(anchor="w", padx=10, pady=10)
            return
        for field in self.fields:
            row = ttk.Frame(self.field_frame, style="Panel.TFrame")
            row.pack(fill="x", padx=10, pady=4)
            label = f"{field['name']}  (p{field['page']}, {field['type']})"
            ttk.Label(row, text=label, style="Panel.TLabel", wraplength=420).pack(anchor="w")
            variable = tk.StringVar(value=str(field["value"] or ""))
            self.entries[field["name"]] = variable
            if field["options"]:
                ttk.Combobox(
                    row, textvariable=variable, values=tuple(field["options"]), state="readonly"
                ).pack(fill="x", pady=(2, 0))
            else:
                ttk.Entry(row, textvariable=variable).pack(fill="x", pady=(2, 0))

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file() or not self.entries:
            messagebox.showwarning(APP_NAME, "Load a PDF form with fields first.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save filled form", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_filled.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        values = {name: variable.get() for name, variable in self.entries.items()}
        self.run_job(
            "Filling form…", lambda: fill_pdf_form(source, output, values),
            lambda result: self._saved(result, f"Filled {result['filled']} field(s).")
        )

    def flatten(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a PDF form.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save flattened form", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_flat.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        self.run_job(
            "Flattening form…", lambda: flatten_pdf_form(source, output),
            lambda result: self._saved(result, f"Flattened {result['flattened']} field(s).")
        )

    def export_fields(self):
        if not self.fields:
            messagebox.showwarning(APP_NAME, "Load a PDF form first.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Export field list", defaultextension=".txt",
            initialfile="form_fields.txt", filetypes=[("Text files", "*.txt")],
        )
        if not output:
            return
        lines = [f"{'PAGE':<6}{'TYPE':<16}{'NAME':<40}VALUE", "-" * 90]
        for field in self.fields:
            lines.append(
                f"{field['page']:<6}{field['type']:<16}{field['name'][:38]:<40}{field['value']}"
            )
        Path(output).write_text("\n".join(lines), encoding="utf-8")
        messagebox.showinfo(APP_NAME, f"Field list exported.\n\n{output}", parent=self)

    def _saved(self, result, message):
        self.preview.load(result["output"])
        messagebox.showinfo(APP_NAME, f"{message}\n\n{result['output']}", parent=self)


class EditPage(BasePage):
    title = "Edit PDF"
    description = "Add text, images and shapes to any page of a PDF."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.file_var = tk.StringVar()
        self.mode_var = tk.StringVar(value="Text")
        self.page_var = tk.IntVar(value=1)
        self.text_var = tk.StringVar()
        self.image_var = tk.StringVar()
        self.shape_var = tk.StringVar(value="Rectangle")
        self.x_var = tk.DoubleVar(value=72)
        self.y_var = tk.DoubleVar(value=72)
        self.w_var = tk.DoubleVar(value=200)
        self.h_var = tk.DoubleVar(value=100)
        self.size_var = tk.IntVar(value=12)
        self.colour_var = tk.StringVar(value="Black")
        self.filled_var = tk.BooleanVar(value=False)

        self.section("Source PDF")
        self.file_row(self.file_var, lambda: self.choose_pdf(self.file_var))

        self.section("What to add")
        mode_row = ttk.Frame(self.controls, style="Panel.TFrame")
        mode_row.pack(fill="x")
        for text in ("Text", "Image", "Shape", "Rotate", "Crop"):
            ttk.Radiobutton(
                mode_row, text=text, value=text, variable=self.mode_var,
                command=self._mode_changed
            ).pack(side="left", padx=(0, 13))

        self.dynamic = ttk.Frame(self.controls, style="Panel.TFrame")
        self.dynamic.pack(fill="x", pady=(10, 0))

        self.text_entry = ttk.Entry(self.dynamic, textvariable=self.text_var)
        self.image_row = ttk.Frame(self.dynamic, style="Panel.TFrame")
        ttk.Entry(self.image_row, textvariable=self.image_var).pack(side="left", fill="x", expand=True)
        ttk.Button(
            self.image_row, text="Choose image", command=self.choose_image, style="Quiet.TButton"
        ).pack(side="left", padx=(8, 0))
        self.shape_combo = ttk.Combobox(
            self.dynamic, textvariable=self.shape_var, state="readonly",
            values=("Rectangle", "Ellipse", "Line", "Highlight"),
        )

        # Rotate controls
        self.rotate_var = tk.StringVar(value="90° clockwise")
        self.rotate_row = ttk.Frame(self.dynamic, style="Panel.TFrame")
        ttk.Label(self.rotate_row, text="Rotate the page shown in the preview by:",
                  style="Panel.TLabel").pack(anchor="w", pady=(0, 4))
        ttk.Combobox(
            self.rotate_row, textvariable=self.rotate_var, state="readonly",
            values=("90° clockwise", "180°", "90° anticlockwise"),
        ).pack(fill="x")

        # Crop controls
        self.crop_unit_var = tk.StringVar(value="points")
        self.crop_l = tk.DoubleVar(value=0)
        self.crop_t = tk.DoubleVar(value=0)
        self.crop_r = tk.DoubleVar(value=0)
        self.crop_b = tk.DoubleVar(value=0)
        self.crop_row = ttk.Frame(self.dynamic, style="Panel.TFrame")
        unit = ttk.Frame(self.crop_row, style="Panel.TFrame")
        unit.pack(fill="x", pady=(0, 6))
        ttk.Label(unit, text="Margins to remove, unit:", style="Panel.TLabel").pack(
            side="left", padx=(0, 8)
        )
        ttk.Combobox(
            unit, textvariable=self.crop_unit_var, state="readonly",
            values=("points", "percent"), width=10,
        ).pack(side="left")
        crop_grid = ttk.Frame(self.crop_row, style="Panel.TFrame")
        crop_grid.pack(fill="x")
        for column, (label, variable) in enumerate((
            ("Left", self.crop_l), ("Top", self.crop_t),
            ("Right", self.crop_r), ("Bottom", self.crop_b),
        )):
            crop_grid.columnconfigure(column, weight=1)
            ttk.Label(crop_grid, text=label, style="Panel.TLabel").grid(
                row=0, column=column, sticky="w", padx=(0, 6)
            )
            ttk.Spinbox(
                crop_grid, from_=0, to=500, increment=5,
                textvariable=variable, width=8,
            ).grid(row=1, column=column, sticky="ew", padx=(0, 6))

        self.text_entry.pack(fill="x")

        # Page navigation tied to the preview
        nav = ttk.Frame(self.controls, style="Panel.TFrame")
        nav.pack(fill="x", pady=(10, 0))
        ttk.Button(nav, text="‹ Previous page", style="Quiet.TButton",
                   command=lambda: self._step_page(-1)).pack(side="left")
        ttk.Button(nav, text="Next page ›", style="Quiet.TButton",
                   command=lambda: self._step_page(1)).pack(side="left", padx=(6, 0))
        ttk.Button(nav, text="Show this page in preview", style="Quiet.TButton",
                   command=self._sync_preview).pack(side="left", padx=(6, 0))

        self.section("Position and size (PDF points, origin top-left)")
        grid = ttk.Frame(self.controls, style="Panel.TFrame")
        grid.pack(fill="x")
        for column in range(2):
            grid.columnconfigure(column, weight=1)
        specs = (
            ("Page number", self.page_var, 0, 0),
            ("Font size", self.size_var, 0, 1),
            ("X position", self.x_var, 1, 0),
            ("Y position", self.y_var, 1, 1),
            ("Width", self.w_var, 2, 0),
            ("Height", self.h_var, 2, 1),
        )
        for label, variable, row, column in specs:
            padx = (0, 8) if column == 0 else (8, 0)
            ttk.Label(grid, text=label, style="Panel.TLabel").grid(
                row=row * 2, column=column, sticky="w", padx=padx, pady=(8, 3)
            )
            ttk.Spinbox(
                grid, from_=0, to=2000, increment=5, textvariable=variable
            ).grid(row=row * 2 + 1, column=column, sticky="ew", padx=padx)

        options = ttk.Frame(self.controls, style="Panel.TFrame")
        options.pack(fill="x", pady=(12, 0))
        ttk.Label(options, text="Colour", style="Panel.TLabel").pack(side="left", padx=(0, 8))
        ttk.Combobox(
            options, textvariable=self.colour_var, state="readonly", width=14,
            values=("Black", "Red", "Blue", "Green", "Orange", "Grey"),
        ).pack(side="left")
        ttk.Checkbutton(
            options, text="Fill shape", variable=self.filled_var
        ).pack(side="left", padx=(16, 0))

        ttk.Label(
            self.controls,
            text="A4 page is 595 × 842 points. Y is measured from the top of the page. "
                 "Use the preview panel to judge placement, then adjust and re-run.",
            style="Help.TLabel", wraplength=500,
        ).pack(anchor="w", pady=(12, 0))

        ttk.Button(
            self.controls, text="Apply Edit and Save", command=self.process,
            style="Primary.TButton"
        ).pack(fill="x", pady=(14, 0), ipady=4)

    COLOURS = {
        "Black": (0, 0, 0), "Red": (0.85, 0.12, 0.12), "Blue": (0.11, 0.37, 0.64),
        "Green": (0.15, 0.5, 0.25), "Orange": (0.91, 0.53, 0.10), "Grey": (0.45, 0.45, 0.45),
    }

    def _mode_changed(self):
        for widget in (self.text_entry, self.image_row, self.shape_combo,
                       self.rotate_row, self.crop_row):
            widget.pack_forget()
        mode = self.mode_var.get()
        if mode == "Text":
            self.text_entry.pack(fill="x")
        elif mode == "Image":
            self.image_row.pack(fill="x")
        elif mode == "Shape":
            self.shape_combo.pack(fill="x")
        elif mode == "Rotate":
            self.rotate_row.pack(fill="x")
        elif mode == "Crop":
            self.crop_row.pack(fill="x")

    def _step_page(self, delta: int):
        """Move the page selector and mirror it in the preview."""
        try:
            current = int(self.page_var.get())
        except Exception:
            current = 1
        target = max(1, current + delta)
        source = self.file_var.get().strip()
        if Path(source).is_file():
            try:
                pymupdf = get_pymupdf()
                doc = pymupdf.open(source)
                target = min(target, doc.page_count)
                doc.close()
            except Exception:
                pass
        self.page_var.set(target)
        self._sync_preview()

    def _sync_preview(self):
        """Show the page currently selected for editing in the preview pane."""
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a source PDF first.", parent=self)
            return
        try:
            index = max(0, int(self.page_var.get()) - 1)
        except Exception:
            index = 0
        self.preview.load(source, page=index)

    def choose_image(self):
        path = filedialog.askopenfilename(
            parent=self, title="Select image",
            filetypes=[("Images", "*.png *.jpg *.jpeg *.bmp *.webp")],
        )
        if path:
            self.image_var.set(path)

    def preview_source(self):
        return self.file_var.get().strip()

    def build_preview_job(self, temporary):
        source = self.preview_source()
        mode = self.mode_var.get()
        page_index = max(0, int(self.page_var.get()) - 1)
        colour = self.COLOURS.get(self.colour_var.get(), (0, 0, 0))
        x, y = float(self.x_var.get()), float(self.y_var.get())
        w, h = float(self.w_var.get()), float(self.h_var.get())
        if mode == "Rotate":
            degrees = {"90° clockwise": 90, "180°": 180,
                       "90° anticlockwise": 270}[self.rotate_var.get()]
            return lambda: edit_page_transform(
                source, temporary, page_index, rotate_degrees=degrees
            )
        if mode == "Crop":
            crop = (float(self.crop_l.get()), float(self.crop_t.get()),
                    float(self.crop_r.get()), float(self.crop_b.get()))
            if not any(crop):
                raise FeatureError("Enter at least one crop margin.")
            unit = self.crop_unit_var.get()
            return lambda: edit_page_transform(
                source, temporary, page_index, crop=crop, crop_unit=unit
            )
        if mode == "Text":
            if not self.text_var.get().strip():
                raise FeatureError("Enter the text to add.")
            text, size = self.text_var.get(), int(self.size_var.get())
            return lambda: edit_pdf_add_text(
                source, temporary, page_index, text, x, y, size, colour
            )
        if mode == "Image":
            if not Path(self.image_var.get()).is_file():
                raise FeatureError("Choose an image file.")
            image = self.image_var.get()
            return lambda: edit_pdf_add_image(
                source, temporary, page_index, image, x, y, w, h
            )
        shape = self.shape_var.get()
        filled = bool(self.filled_var.get())
        return lambda: edit_pdf_add_shape(
            source, temporary, page_index, shape,
            x, y, x + w, y + h, colour, 1.5, filled,
        )

    def process(self):
        source = self.file_var.get().strip()
        if not Path(source).is_file():
            messagebox.showwarning(APP_NAME, "Select a source PDF.", parent=self)
            return
        mode = self.mode_var.get()
        if mode == "Text" and not self.text_var.get().strip():
            messagebox.showwarning(APP_NAME, "Enter the text to add.", parent=self)
            return
        if mode == "Image" and not Path(self.image_var.get()).is_file():
            messagebox.showwarning(APP_NAME, "Choose an image file.", parent=self)
            return
        output = filedialog.asksaveasfilename(
            parent=self, title="Save edited PDF", defaultextension=".pdf",
            initialfile=f"{safe_filename(Path(source).stem)}_edited.pdf",
            filetypes=[("PDF files", "*.pdf")],
        )
        if not output:
            return
        page_index = max(0, int(self.page_var.get()) - 1)
        colour = self.COLOURS.get(self.colour_var.get(), (0, 0, 0))
        x, y = float(self.x_var.get()), float(self.y_var.get())
        w, h = float(self.w_var.get()), float(self.h_var.get())

        if mode == "Rotate":
            degrees = {"90° clockwise": 90, "180°": 180,
                       "90° anticlockwise": 270}[self.rotate_var.get()]
            work = lambda: edit_page_transform(
                source, output, page_index, rotate_degrees=degrees,
            )
        elif mode == "Crop":
            crop = (float(self.crop_l.get()), float(self.crop_t.get()),
                    float(self.crop_r.get()), float(self.crop_b.get()))
            if not any(crop):
                messagebox.showwarning(
                    APP_NAME, "Enter at least one crop margin.", parent=self
                )
                return
            work = lambda: edit_page_transform(
                source, output, page_index, crop=crop,
                crop_unit=self.crop_unit_var.get(),
            )
        elif mode == "Text":
            work = lambda: edit_pdf_add_text(
                source, output, page_index, self.text_var.get(),
                x, y, int(self.size_var.get()), colour,
            )
        elif mode == "Image":
            work = lambda: edit_pdf_add_image(
                source, output, page_index, self.image_var.get(), x, y, w, h
            )
        else:
            work = lambda: edit_pdf_add_shape(
                source, output, page_index, self.shape_var.get(),
                x, y, x + w, y + h, colour, 1.5, bool(self.filled_var.get()),
            )
        self.run_job("Applying edit…", work, self._done)

    def _done(self, result):
        page = result.get("page")
        # Reload the preview on the page that was just edited
        try:
            self.preview.load(result["output"], page=max(0, int(page) - 1))
        except Exception:
            self.preview.load(result["output"])
        actions = result.get("actions")
        detail = f"Page {page}: {', '.join(actions)}." if actions else \
                 f"Edit applied to page {page}."
        messagebox.showinfo(
            APP_NAME, f"{detail}\n\n{result['output']}", parent=self
        )


class CertificateDialog(tk.Toplevel):
    def __init__(self, master):
        super().__init__(master)
        self.title("Create test certificate")
        self.geometry("470x390")
        self.resizable(False, False)
        self.configure(bg=COLORS["paper"])
        self.transient(master)
        self.grab_set()
        self.result = None
        self.common_name = tk.StringVar(value="Smart PDF Pro User")
        self.organization = tk.StringVar(value="Taxosmart")
        self.country = tk.StringVar(value="IN")
        self.password = tk.StringVar(value="changeit")
        self.days = tk.IntVar(value=365)
        frame = ttk.Frame(self, style="Panel.TFrame", padding=22)
        frame.pack(fill="both", expand=True, padx=16, pady=16)
        ttk.Label(frame, text="Self-signed test certificate", style="PanelTitle.TLabel").pack(anchor="w")
        for label, variable, show in (
            ("Common name", self.common_name, None), ("Organization", self.organization, None),
            ("Country code", self.country, None), ("Password", self.password, "•"),
            ("Valid days", self.days, None),
        ):
            ttk.Label(frame, text=label, style="Panel.TLabel").pack(anchor="w", pady=(9, 3))
            ttk.Entry(frame, textvariable=variable, show=show).pack(fill="x")
        ttk.Button(frame, text="Create .p12 file", command=self.create, style="Primary.TButton").pack(
            fill="x", pady=(16, 0)
        )

    def create(self):
        output = filedialog.asksaveasfilename(
            parent=self, title="Save test certificate", defaultextension=".p12",
            initialfile=f"{safe_filename(self.common_name.get())}.p12",
            filetypes=[("PKCS#12 certificate", "*.p12")]
        )
        if not output:
            return
        try:
            generate_test_certificate(
                output, self.common_name.get(), self.organization.get(), self.country.get(),
                self.password.get(), int(self.days.get()),
            )
        except Exception as exc:
            messagebox.showerror(APP_NAME, str(exc), parent=self)
            return
        self.result = output
        messagebox.showinfo(
            APP_NAME, f"Test certificate created.\n\n{output}\n\nKeep its password secure.", parent=self
        )
        self.destroy()


class HeroBanner(tk.Canvas):
    """Quiet masthead: white field, thin blue rule, no gradient or ornament."""

    def __init__(self, master):
        super().__init__(
            master, height=132, bd=0, highlightthickness=0, bg=COLORS["white"]
        )
        self.bind("<Configure>", self._draw)

    def _draw(self, _event=None):
        self.delete("all")
        w, h = max(1, self.winfo_width()), max(1, self.winfo_height())
        self.configure(bg=COLORS["white"])

        # Top hairline
        self.create_line(0, 0, w, 0, fill=COLORS["blue_200"])
        # Left accent rule
        self.create_rectangle(0, 24, 3, h - 24, fill=COLORS["blue_700"], outline="")

        self.create_text(
            26, 28, anchor="nw", text="LOCAL PDF WORKSPACE",
            fill=COLORS["blue_500"], font=("Segoe UI", 7, "bold"),
        )
        self.create_text(
            24, 46, anchor="nw", text="Smart PDF Pro",
            fill=COLORS["blue_900"], font=("Segoe UI Semilight", 26),
        )
        self.create_text(
            26, 88, anchor="nw",
            text="Twenty tools for merging, converting, securing and reviewing documents.",
            fill=COLORS["muted"], font=("Segoe UI", 10), width=max(320, w - 200),
        )
        # Bottom hairline
        self.create_line(0, h - 1, w, h - 1, fill=COLORS["blue_200"])


class FeatureCard(tk.Frame):
    """Flat white tile with a hairline border; blue only on hover and glyph."""

    def __init__(self, master, title: str, description: str, icon: str, accent: str, command):
        super().__init__(
            master, bg=COLORS["white"], highlightthickness=1,
            highlightbackground=COLORS["line"], cursor="hand2",
        )
        body = tk.Frame(self, bg=COLORS["white"], padx=15, pady=13)
        body.pack(fill="both", expand=True)

        self.icon_label = tk.Label(
            body, text=icon, bg=COLORS["white"], fg=COLORS["blue_500"],
            font=("Segoe UI", 17), anchor="w",
        )
        self.icon_label.pack(anchor="w")

        self.title_label = tk.Label(
            body, text=title, bg=COLORS["white"], fg=COLORS["blue_900"],
            font=("Segoe UI", 11), anchor="w",
        )
        self.title_label.pack(fill="x", pady=(8, 2))

        self.description_label = tk.Label(
            body, text=description, bg=COLORS["white"], fg=COLORS["muted"],
            font=("Segoe UI", 8), justify="left", anchor="nw", wraplength=150,
        )
        self.description_label.pack(fill="both", expand=True)

        self._parts = (self, body, self.icon_label, self.title_label, self.description_label)
        for widget in self._parts:
            widget.bind("<Button-1>", lambda _e: command())
            widget.bind("<Enter>", lambda _e: self._hover(True))
            widget.bind("<Leave>", lambda _e: self._hover(False))

    def _hover(self, active: bool):
        background = COLORS["blue_050"] if active else COLORS["white"]
        self.configure(
            highlightbackground=COLORS["blue_300"] if active else COLORS["line"],
            highlightthickness=1,
            bg=background,
        )
        for widget in self._parts[1:]:
            try:
                widget.configure(bg=background)
            except Exception:
                pass
        self.icon_label.configure(fg=COLORS["blue_700"] if active else COLORS["blue_500"])


class WelcomePage(ttk.Frame):
    def __init__(self, master, app: "SmartPDFPro"):
        super().__init__(master, style="App.TFrame")

        # Scrollable body so every tool tile stays reachable on short screens
        canvas = tk.Canvas(self, bg=COLORS["paper"], highlightthickness=0)
        scroll = ttk.Scrollbar(self, orient="vertical", command=canvas.yview)
        inner = ttk.Frame(canvas, style="App.TFrame", padding=22)
        window = canvas.create_window((0, 0), window=inner, anchor="nw")

        def _sync(_event=None):
            canvas.configure(scrollregion=canvas.bbox("all"))
            canvas.itemconfigure(window, width=canvas.winfo_width())

        inner.bind("<Configure>", _sync)
        canvas.bind("<Configure>", _sync)
        canvas.configure(yscrollcommand=scroll.set)
        scroll.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)

        def _wheel(event):
            step = -1 if getattr(event, "num", 0) == 5 or getattr(event, "delta", 0) < 0 else 1
            canvas.yview_scroll(-step, "units")
            return "break"

        def _bind_wheel(widget):
            for sequence in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                widget.bind(sequence, _wheel)
            for child in widget.winfo_children():
                _bind_wheel(child)

        self._canvas, self._inner, self._bind_wheel = canvas, inner, _bind_wheel

        HeroBanner(inner).pack(fill="x", pady=(0, 18))
        cards = ttk.Frame(inner, style="App.TFrame")
        cards.pack(fill="both", expand=True)
        for column in range(5):
            cards.columnconfigure(column, weight=1, uniform="card")
        A = COLORS["blue_700"]
        tools = [
            ("Merge",        "Combine PDFs in order",      "⧉", A, "merge"),
            ("Compiler",     "Build appeal paper books",   "📚", A, "compiler"),
            ("Split",        "Five splitting modes",       "⑃", A, "split"),
            ("Organize",     "Reorder & remove pages",     "☰", A, "organize"),
            ("Rotate",       "Rotate selected pages",      "↻", A, "rotate"),
            ("Crop",         "Trim page margins",          "⬚", A, "crop"),
            ("Compress",     "Three quality levels",       "⇩", A, "compress"),
            ("Repair",       "Rebuild damaged files",      "⚒", A, "repair"),
            ("OCR",          "Make scans searchable",      "⌕", A, "ocr"),
            ("Convert",      "Word, Excel, PPT, HTML",     "⇄", A, "convert"),
            ("Scan to PDF",  "Photos to clean PDF",        "⎙", A, "scan"),
            ("Translate",    "Indian languages",           "अ", A, "translate"),
            ("PDF Downloader", "Download PDFs from webpages", "⬇", A, "downloader"),
            ("Edit",         "Text, images & shapes",      "✎", A, "edit"),
            ("Watermark",    "Text & image marks",         "◈", A, "watermark"),
            ("Page Numbers", "Any format or position",     "№", A, "numbers"),
            ("Protect",      "AES-256 encryption",         "🔒", A, "protect"),
            ("Unlock",       "Remove known password",      "🔓", A, "unlock"),
            ("Unprotect",    "Remove restrictions",        "🗝", A, "unprotect"),
            ("Redact",       "Manual & smart redaction",   "▮", A, "redact"),
            ("Digital Sign", "PKCS#12 sign & verify",      "✓", A, "sign"),
            ("PDF Forms",    "Fill & flatten forms",       "▤", A, "forms"),
            ("Compare",      "Find text differences",      "⇅", A, "compare"),
        ]
        for index, (title, text, icon, accent, key) in enumerate(tools):
            card = FeatureCard(
                cards, title, text, icon, accent, command=lambda k=key: app.show(k)
            )
            card.grid(row=index // 5, column=index % 5, sticky="nsew", padx=3, pady=3)
        note = tk.Frame(inner, bg=COLORS["blue_050"], padx=16, pady=11)
        note.pack(fill="x", pady=(18, 0))
        tk.Frame(note, bg=COLORS["blue_500"], width=2).pack(side="left", fill="y", padx=(0, 12))
        tk.Label(
            note,
            text="Editing tools run locally. Translate and PDF Downloader use the internet; "
                 "the Downloader visits only the webpage and PDF links you provide.",
            bg=COLORS["blue_050"], fg=COLORS["blue_800"],
            font=("Segoe UI", 9), justify="left", anchor="w",
        ).pack(side="left", anchor="w")

        self._cards_frame = cards
        self._card_widgets = [w for w in cards.winfo_children()]
        self.after(200, lambda: _bind_wheel(self))

        def _regrid(_event=None):
            """Choose the number of tile columns to suit the available width."""
            width = canvas.winfo_width()
            if width < 100:
                return
            columns = max(2, min(6, width // 235))
            if columns == getattr(self, "_columns", None):
                return
            self._columns = columns
            for column in range(6):
                cards.columnconfigure(column, weight=1 if column < columns else 0,
                                      uniform="card" if column < columns else "")
            for index, widget in enumerate(self._card_widgets):
                widget.grid_configure(row=index // columns, column=index % columns)

        canvas.bind("<Configure>", lambda e: (_sync(e), _regrid(e)))
        self.after(240, _regrid)


class HelpPage(ttk.Frame):
    def __init__(self, master, app):
        super().__init__(master, style="App.TFrame", padding=30)
        ttk.Label(self, text="Setup & Help", style="Title.TLabel").pack(anchor="w")
        ttk.Label(
            self, text="The program is a single source file; feature libraries are installed separately.",
            style="Subtitle.TLabel"
        ).pack(anchor="w", pady=(4, 18))
        box = tk.Text(
            self, bg=COLORS["panel"], fg=COLORS["ink"], bd=0, padx=20, pady=18,
            highlightthickness=1, highlightbackground=COLORS["line"], wrap="word",
            font=("Consolas", 10), spacing2=3,
        )
        help_scroll = ttk.Scrollbar(self, orient="vertical", command=box.yview)
        box.configure(yscrollcommand=help_scroll.set)
        help_scroll.pack(side="right", fill="y")
        box.pack(side="left", fill="both", expand=True)

        def _help_wheel(event):
            step = -1 if getattr(event, "num", 0) == 5 or getattr(event, "delta", 0) < 0 else 1
            box.yview_scroll(-step, "units")
            return "break"

        for sequence in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            box.bind(sequence, _help_wheel)
        command = (
            f"{sys.executable} -m pip install pypdf pymupdf pillow pdf2docx pdfplumber "
            "openpyxl xlsxwriter python-docx python-pptx reportlab pytesseract cryptography "
            "\"pyHanko[image-support,opentype]\" pyhanko-certvalidator "
            "deep-translator langdetect pymupdf4llm argostranslate"
        )
        content = f"""QUICK START

1. Install the recommended packages:

{command}

2. Run this file:

{sys.executable} {Path(__file__).name}

OPTIONAL SYSTEM SOFTWARE

• Tesseract OCR: only needed for scanned/image-only PDFs.
  Selectable-text PDFs do NOT require Tesseract (just untick 'Use OCR').
  Windows installer: https://github.com/UB-Mannheim/tesseract/wiki
    Tick “Additional language data” and select Hindi (hin), Gujarati (guj), Marathi (mar).
  macOS: brew install tesseract tesseract-lang
  Linux: sudo apt install tesseract-ocr tesseract-ocr-hin tesseract-ocr-guj
  Use “Locate Tesseract” in the Translate screen if not auto-detected.
  Guide: https://tesseract-ocr.github.io/tessdoc/Installation.html
• Microsoft Office (Windows) or LibreOffice improves Word/Excel → PDF fidelity.

OPTIONAL PIP PACKAGES

• pywin32 — Microsoft Word/Excel automation on Windows.
• pymupdf-fonts — additional font coverage for multilingual PDF output.

PACKAGE PURPOSES

• pypdf + reportlab + xlsxwriter — Compiler paper books, indexes, dividers and pagination.
• pypdf — merge, split, organize, page rotation.
• pymupdf + pillow — preview, watermark, crop, redact, protect, compress,
  page numbers, edit, OCR rendering, translate, repair, compare.
• pdfplumber + openpyxl — table extraction and formatted Excel output.
• pdf2docx + python-docx + reportlab — Word/PDF conversion.
• python-pptx — PDF → PowerPoint slide export.
• pymupdf4llm — high-quality PDF → Markdown (optional but recommended).
• pytesseract — OCR for scanned documents (needs the Tesseract binary).
• langdetect — automatic source-language detection (fully offline).
• deep-translator — Online translation engine (Google Translate / MyMemory, internet required).
• argostranslate — Offline translation engine (fully local once language packs are
  downloaded once; see "Translate PDF" screen). Covers English, Hindi, Bengali, Urdu,
  Arabic, Chinese, Japanese, French, German, Spanish only — other Indian languages
  (Marathi, Gujarati, Tamil, Telugu, Kannada, Malayalam, Punjabi, Odia, Assamese,
  Sanskrit, Nepali) still need the Online engine.
• cryptography + pyHanko — PKCS#12 certificates and PAdES digital signatures.

GHOSTSCRIPT (optional — only for certified PDF/A output)

• Without Ghostscript, "PDF → PDF/A" produces a cleaned PDF, not a certified
  PDF/A file. For true archival compliance install Ghostscript:
    Windows: https://ghostscript.com/releases/gsdnld.html
    macOS:   brew install ghostscript
    Linux:   sudo apt install ghostscript

TOOL REFERENCE (22 tools)

ORGANISE   Merge · Compiler · Split · Organize Pages · Rotate · Crop
OPTIMISE   Compress · Repair · OCR PDF
CONVERT    Convert (Word/Excel/PPT/HTML/Markdown/PDF-A/images) · Scan to PDF · Translate
WEB        PDF Downloader
EDIT       Edit PDF · Watermark · Page Numbers
SECURITY   Protect · Unlock · Redact · Digital Sign
REVIEW     PDF Forms · Compare

NOTES

• Maximum input size is 500 MB per file.
• Existing output files are written only after you confirm the Save dialog.
• Compiler provides separate actions to create the PDF index, create/open the Excel index,
  save the complete paper book and open the compiled PDF.
• Split outputs are automatically renamed if the same filename already exists.
• PDF preview requires PyMuPDF and Pillow.
• Self-signed certificates are for testing and do not replace a trusted DSC.
• High compression may visibly reduce embedded-image quality.
• Translation sends extracted text to the online provider and creates a clean reflowed PDF.
• PDF Downloader accesses the webpage URL and PDF links entered by the user.
• Current pyHanko releases require Python 3.10 or later.
• Redaction is permanent — text and image pixels are destroyed in the output.
• Smart Redaction is pattern-based and runs locally. Review every selected match before saving.
• Scanned PDFs must be processed with OCR before text search or smart detection can find text.
• Crop hides content outside the crop box; use Redact to truly remove it.
• Unlock PDF requires the correct password; it does not crack encryption.
• PDF → PowerPoint exports each page as a full-slide image, not editable text.
• HTML → PDF supports basic HTML/CSS only — no JavaScript or external stylesheets.
• Compare PDF matches text content; it does not compare images or layout.
• PDF Forms works on interactive (AcroForm) PDFs; flat forms need Edit PDF.

PYTHON

{sys.version}
Platform: {platform.platform()}
"""
        box.insert("1.0", content)
        box.configure(state="disabled")


class LicenseGate(tk.Frame):
    """Full-window screen shown when neither trial nor license permits use.

    This replaces the shell entirely (rather than disabling individual pages)
    so there is exactly one place that decides "can this session run".
    """

    def __init__(self, master, app: "SmartPDFPro"):
        super().__init__(master, bg=COLORS["paper"])
        self.app = app
        wrap = tk.Frame(self, bg=COLORS["paper"])
        wrap.place(relx=0.5, rely=0.5, anchor="center")

        card = tk.Frame(
            wrap, bg=COLORS["white"], highlightthickness=1,
            highlightbackground=COLORS["line"], padx=36, pady=32,
        )
        card.pack()

        logo = load_logo("hero", 64)
        if logo is not None:
            tk.Label(card, image=logo, bg=COLORS["white"]).pack(pady=(0, 14))
            self._logo_ref = logo

        tk.Label(
            card, text="Trial period has ended", bg=COLORS["white"],
            fg=COLORS["blue_900"], font=("Segoe UI Semilight", 20),
        ).pack()
        tk.Label(
            card,
            text="Your 180-day free trial of Smart PDF Pro has finished.\n"
                 "Enter a license key to keep using the application.",
            bg=COLORS["white"], fg=COLORS["muted"], font=("Segoe UI", 10),
            justify="center",
        ).pack(pady=(8, 20))

        self.key_var = tk.StringVar()
        entry = ttk.Entry(
            card, textvariable=self.key_var, font=("Consolas", 13),
            justify="center", width=32,
        )
        entry.pack(ipady=6)
        entry.bind("<KeyRelease>", self._auto_format)

        self.error_var = tk.StringVar()
        tk.Label(
            card, textvariable=self.error_var, bg=COLORS["white"],
            fg=COLORS["danger"], font=("Segoe UI", 9),
        ).pack(pady=(8, 0))

        ttk.Button(
            card, text="Activate", style="Primary.TButton", command=self.activate,
        ).pack(fill="x", pady=(14, 0), ipady=5)

        tk.Label(
            card, text="Need a license key? Contact Tax-O-Smart.",
            bg=COLORS["white"], fg=COLORS["blue_600"], font=("Segoe UI", 9),
        ).pack(pady=(16, 0))

    def _auto_format(self, _event=None):
        raw = normalize_license_key(self.key_var.get())[:LICENSE_TOTAL_LEN]
        formatted = format_license_key(raw) if raw else ""
        if formatted != self.key_var.get():
            self.key_var.set(formatted)
            self.key_var.set(formatted)  # noqa: keep cursor logic simple
            try:
                entry_widget = self.focus_get()
                if entry_widget is not None:
                    entry_widget.icursor("end")
            except Exception:
                pass

    def activate(self):
        try:
            activate_license(self.key_var.get())
        except FeatureError as exc:
            self.error_var.set(str(exc).splitlines()[0])
            return
        self.app.refresh_license_state()


class LicensePage(BasePage):
    title = "License"
    description = "View your trial or license status, and activate a license key."

    def __init__(self, master, app):
        super().__init__(master, app)
        self.controls.grid_forget() if False else None  # keep BasePage layout

        self.section("Status")
        self.status_box = tk.Frame(
            self.controls, bg=COLORS["blue_050"], highlightthickness=1,
            highlightbackground=COLORS["blue_200"], padx=16, pady=14,
        )
        self.status_box.pack(fill="x")
        self.status_title = tk.Label(
            self.status_box, text="", bg=COLORS["blue_050"], fg=COLORS["blue_900"],
            font=("Segoe UI Semilight", 15), anchor="w",
        )
        self.status_title.pack(anchor="w")
        self.status_detail = tk.Label(
            self.status_box, text="", bg=COLORS["blue_050"], fg=COLORS["blue_800"],
            font=("Segoe UI", 10), anchor="w", justify="left", wraplength=480,
        )
        self.status_detail.pack(anchor="w", pady=(4, 0))

        self.section("Activate a license key")
        row = ttk.Frame(self.controls, style="Panel.TFrame")
        row.pack(fill="x")
        self.key_var = tk.StringVar()
        entry = ttk.Entry(
            row, textvariable=self.key_var, font=("Consolas", 11), width=30,
        )
        entry.pack(side="left", fill="x", expand=True)
        entry.bind("<KeyRelease>", self._auto_format)
        ttk.Button(
            row, text="Activate", style="Primary.TButton", command=self.activate,
        ).pack(side="left", padx=(8, 0))
        ttk.Label(
            self.controls,
            text="A license activates for 365 days from the day it is entered. "
                 "Keys are 25 characters and never use the letters 0, O, 1 or I.",
            style="Help.TLabel", wraplength=520,
        ).pack(anchor="w", pady=(6, 0))

        self.refresh()

    def _auto_format(self, _event=None):
        raw = normalize_license_key(self.key_var.get())[:LICENSE_TOTAL_LEN]
        formatted = format_license_key(raw) if raw else ""
        if formatted != self.key_var.get():
            self.key_var.set(formatted)

    def activate(self):
        try:
            activate_license(self.key_var.get())
        except FeatureError as exc:
            messagebox.showwarning(APP_NAME, str(exc), parent=self)
            return
        self.app.refresh_license_state()
        self.refresh()
        messagebox.showinfo(
            APP_NAME, "License activated. Valid for 365 days.", parent=self
        )

    def refresh(self):
        status = get_license_status()
        mode = status["mode"]
        if mode == "licensed":
            self.status_title.configure(text="✔ Licensed")
            self.status_detail.configure(
                text=f"Key: {status['license_key']}\n"
                     f"{status['days_remaining']} day(s) remaining on this activation."
            )
        elif mode == "trial":
            self.status_title.configure(text="Free trial")
            self.status_detail.configure(
                text=f"{status['days_remaining']} of {TRIAL_DAYS} trial day(s) remaining. "
                     "Activate a license key at any time to continue after the trial ends."
            )
        else:
            self.status_title.configure(text="Trial ended")
            self.status_detail.configure(
                text="Enter a valid license key below to keep using the application."
            )


class SmartPDFPro(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"{APP_NAME}  ·  Taxosmart")
        self.geometry("1400x900")
        self.minsize(1160, 750)
        self.configure(bg=COLORS["paper"])
        self._configure_style()
        self.protocol("WM_DELETE_WINDOW", self._on_close)

        # ── Brand bar: Tax-O-Smart top-left, Smart PDF Pro shield top-right ──
        brand = tk.Frame(self, bg=COLORS["white"], height=62)
        brand.pack(fill="x", side="top")
        brand.pack_propagate(False)

        self.logo_left_label = tk.Label(brand, bg=COLORS["white"])
        self.logo_left_label.pack(side="left", padx=(18, 0), pady=8)

        self.logo_right_label = tk.Label(brand, bg=COLORS["white"])
        self.logo_right_label.pack(side="right", padx=(0, 18), pady=8)

        centre = tk.Frame(brand, bg=COLORS["white"])
        centre.pack(side="right", padx=(0, 12))
        self.brand_title = tk.Label(
            centre, text="Smart PDF Pro", bg=COLORS["white"], fg=COLORS["blue_900"],
            font=("Segoe UI Semilight", 15), anchor="e",
        )
        self.brand_title.pack(anchor="e")
        self.brand_sub = tk.Label(
            centre, text="Local PDF workspace", bg=COLORS["white"],
            fg=COLORS["muted"], font=("Segoe UI", 8), anchor="e",
        )
        self.brand_sub.pack(anchor="e")

        tk.Frame(self, bg=COLORS["blue_300"], height=2).pack(fill="x", side="top")
        self._apply_logos(44)

        shell = ttk.Frame(self, style="App.TFrame")
        shell.pack(fill="both", expand=True)

        # ── Light sidebar: white, scrollable, hairline blue rule ──────────
        self._nav_headings = []
        sidebar_wrap = tk.Frame(shell, bg=COLORS["line"], width=249)
        self._sidebar_wrap = sidebar_wrap
        sidebar_wrap.pack(side="left", fill="y")
        sidebar_wrap.pack_propagate(False)
        sidebar_outer = tk.Frame(sidebar_wrap, bg=COLORS["white"], width=248)
        self._sidebar_outer = sidebar_outer
        sidebar_outer.pack(side="left", fill="both", expand=True)
        sidebar_outer.pack_propagate(False)

        # Wordmark (fixed, does not scroll)
        logo_frame = tk.Frame(sidebar_outer, bg=COLORS["white"], padx=20, pady=17)
        logo_frame.pack(fill="x")
        self._logo_wordmark = tk.Label(
            logo_frame, text="Smart PDF Pro", bg=COLORS["white"], fg=COLORS["blue_900"],
            font=("Segoe UI Semilight", 16), anchor="w",
        )
        self._logo_wordmark.pack(anchor="w")
        self._logo_tagline = tk.Label(
            logo_frame, text="TAX-O-SMART  ·  V5.0", bg=COLORS["white"], fg=COLORS["blue_500"],
            font=("Segoe UI", 7, "bold"),
        )
        self._logo_tagline.pack(anchor="w", pady=(2, 0))
        tk.Frame(sidebar_outer, bg=COLORS["blue_200"], height=1).pack(fill="x", padx=20)

        # Footer (fixed, packed before the scroll area claims the space)
        footer = tk.Frame(sidebar_outer, bg=COLORS["white"])
        footer.pack(side="bottom", fill="x", padx=22, pady=(6, 10))
        tk.Label(
            footer, text="Local processing  ·  No upload",
            bg=COLORS["white"], fg=COLORS["muted"], font=("Segoe UI", 8),
        ).pack(anchor="w")
        self.license_status_var = tk.StringVar(value="")
        self.license_status_label = tk.Label(
            footer, textvariable=self.license_status_var,
            bg=COLORS["white"], fg=COLORS["muted"], font=("Segoe UI", 8, "bold"),
            cursor="hand2",
        )
        self.license_status_label.pack(anchor="w", pady=(2, 0))
        self.license_status_label.bind("<Button-1>", lambda _e: self.show("license"))
        tk.Frame(sidebar_outer, bg=COLORS["blue_200"], height=1).pack(
            fill="x", side="bottom", padx=20
        )

        # Scrollable navigation area
        nav_canvas = tk.Canvas(
            sidebar_outer, bg=COLORS["white"], bd=0, highlightthickness=0
        )
        nav_scroll = ttk.Scrollbar(
            sidebar_outer, orient="vertical", command=nav_canvas.yview
        )
        sidebar = tk.Frame(nav_canvas, bg=COLORS["white"])
        nav_window = nav_canvas.create_window((0, 0), window=sidebar, anchor="nw")

        def _sync(_event=None):
            nav_canvas.configure(scrollregion=nav_canvas.bbox("all"))
            nav_canvas.itemconfigure(nav_window, width=nav_canvas.winfo_width())

        sidebar.bind("<Configure>", _sync)
        nav_canvas.bind("<Configure>", _sync)
        nav_canvas.configure(yscrollcommand=nav_scroll.set)
        # Scrollbar is packed FIRST and stays visible, so it is always obvious
        # that the tool list continues below the fold.
        nav_scroll.pack(side="right", fill="y")
        nav_canvas.pack(side="left", fill="both", expand=True)

        def _nav_wheel(event):
            step = -1 if getattr(event, "num", 0) == 5 or getattr(event, "delta", 0) < 0 else 1
            nav_canvas.yview_scroll(-step, "units")
            return "break"

        # Bind to the canvas and every child so the wheel works anywhere
        # over the sidebar, without hijacking the rest of the window.
        def _bind_nav_wheel(widget):
            for sequence in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                widget.bind(sequence, _nav_wheel)
        _bind_nav_wheel(nav_canvas)
        _bind_nav_wheel(sidebar)
        self._bind_nav_wheel = _bind_nav_wheel

        self.nav_buttons: dict[str, tk.Button] = {}
        nav_groups = [
            (None, [("home", "⌂", "Home")]),
            ("ORGANISE", [
                ("merge",     "⧉", "Merge PDF"),
                ("compiler",  "📚", "Compiler"),
                ("split",     "⑃", "Split PDF"),
                ("organize",  "☰", "Organize Pages"),
                ("rotate",    "↻", "Rotate PDF"),
                ("crop",      "⬚", "Crop PDF"),
            ]),
            ("OPTIMISE", [
                ("compress",  "⇩", "Compress PDF"),
                ("repair",    "⚒", "Repair PDF"),
                ("ocr",       "⌕", "OCR PDF"),
            ]),
            ("CONVERT", [
                ("convert",   "⇄", "Convert"),
                ("scan",      "⎙", "Scan to PDF"),
                ("translate", "अ", "Translate PDF"),
            ]),
            ("WEB", [
                ("downloader", "⬇", "PDF Downloader"),
            ]),
            ("EDIT", [
                ("edit",      "✎", "Edit PDF"),
                ("watermark", "◈", "Watermark"),
                ("numbers",   "№", "Page Numbers"),
            ]),
            ("SECURITY", [
                ("protect",   "🔒", "Protect PDF"),
                ("unlock",    "🔓", "Unlock PDF"),
                ("unprotect", "🗝", "Unprotect PDF"),
                ("redact",    "▮", "Redact PDF"),
                ("sign",      "✓", "Digital Sign"),
            ]),
            ("REVIEW", [
                ("forms",     "▤", "PDF Forms"),
                ("compare",   "⇅", "Compare PDF"),
            ]),
            (None, [("license", "◆", "License"), ("help", "?", "Setup & Help")]),
        ]
        for heading, items in nav_groups:
            if heading:
                _heading_label = tk.Label(
                    sidebar, text=heading, bg=COLORS["white"], fg=COLORS["blue_500"],
                    font=("Segoe UI", 7, "bold"), anchor="w",
                )
                _heading_label.pack(fill="x", padx=(20, 0), pady=(11, 2))
                self._bind_nav_wheel(_heading_label)
                self._nav_headings.append(_heading_label)
            for key, glyph, label in items:
                button = tk.Button(
                    sidebar, text=f"   {glyph}    {label}",
                    command=lambda k=key: self.show(k),
                    bg=COLORS["white"], fg=COLORS["blue_800"],
                    activebackground=COLORS["blue_050"], activeforeground=COLORS["blue_900"],
                    bd=0, relief="flat", overrelief="flat",
                    highlightthickness=0, anchor="w",
                    padx=8, pady=5, font=("Segoe UI", 10), cursor="hand2",
                )
                button.pack(fill="x", padx=(8, 8), pady=1)
                self._bind_nav_wheel(button)
                self.nav_buttons[key] = button
        sidebar.pack_configure(pady=(4, 8))

        self.content = ttk.Frame(shell, style="App.TFrame")
        self.content.pack(side="left", fill="both", expand=True)
        self.pages = {
            "home":      WelcomePage(self.content, self),
            # Organise
            "merge":     MergePage(self.content, self),
            "compiler":  CompilerPage(self.content, self),
            "split":     SplitPage(self.content, self),
            "organize":  OrganizePage(self.content, self),
            "rotate":    RotatePage(self.content, self),
            "crop":      CropPage(self.content, self),
            # Optimise
            "compress":  CompressPage(self.content, self),
            "repair":    RepairPage(self.content, self),
            "ocr":       OcrPage(self.content, self),
            # Convert
            "convert":   ConvertPage(self.content, self),
            "scan":      ScanPage(self.content, self),
            "translate": TranslatePage(self.content, self),
            # Web
            "downloader": DownloaderPage(self.content, self),
            # Edit
            "edit":      EditPage(self.content, self),
            "watermark": WatermarkPage(self.content, self),
            "numbers":   PageNumbersPage(self.content, self),
            # Security
            "protect":   ProtectPage(self.content, self),
            "unlock":    UnlockPage(self.content, self),
            "unprotect": UnprotectPage(self.content, self),
            "redact":    RedactPage(self.content, self),
            "sign":      SignPage(self.content, self),
            # Review
            "forms":     FormsPage(self.content, self),
            "compare":   ComparePage(self.content, self),
            "license":   LicensePage(self.content, self),
            "help":      HelpPage(self.content, self),
        }
        self.show("home")

        # Responsive layout: react to resizing, maximising and DPI changes
        self._layout_name = None
        self._layout_scale = 1.0
        self.bind("<Configure>", self._on_resize)
        self.after(160, self._on_resize)

        # Licensing: block the workspace outright if neither trial nor a
        # valid license currently permits use.
        self._license_gate = None
        self.refresh_license_state()

    def refresh_license_state(self):
        """Re-check trial/license status and show or hide the block screen."""
        status = get_license_status()
        # Sidebar status line
        if hasattr(self, "license_status_var"):
            if status["mode"] == "licensed":
                self.license_status_var.set(f"Licensed · {status['days_remaining']}d left")
                self.license_status_label.configure(foreground=COLORS["blue_700"])
            elif status["mode"] == "trial":
                self.license_status_var.set(f"Trial · {status['days_remaining']}d left")
                self.license_status_label.configure(
                    foreground=COLORS["warning"] if status["days_remaining"] <= 14
                    else COLORS["muted"]
                )
            else:
                self.license_status_var.set("Trial ended")
                self.license_status_label.configure(foreground=COLORS["danger"])
        # Refresh the License page if it exists and is visible
        license_page = self.pages.get("license") if hasattr(self, "pages") else None
        if license_page is not None:
            try:
                license_page.refresh()
            except Exception:
                pass
        # Full-window block when access is not allowed
        if not status["allowed"]:
            if self._license_gate is None:
                self._license_gate = LicenseGate(self, self)
            self._license_gate.place(relx=0, rely=0, relwidth=1, relheight=1)
            self._license_gate.lift()
        elif self._license_gate is not None:
            self._license_gate.place_forget()

    def _configure_style(self):
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        C = COLORS
        P, PNL, SOFT = C["paper"], C["panel"], C["soft"]
        INK, MUTED, LINE = C["ink"], C["muted"], C["line"]
        ACC, ACC_D = C["blue_700"], C["blue_900"]
        FIELD = C["blue_050"]

        style.configure("App.TFrame",    background=P)
        style.configure("Panel.TFrame",  background=PNL)
        style.configure("Card.TFrame",   background=PNL, relief="solid", borderwidth=1)
        style.configure("Notice.TFrame", background=C["blue_100"])

        # ── Labels ──
        style.configure("TLabel",          background=P,   foreground=INK,   font=("Segoe UI", 10))
        style.configure("Panel.TLabel",    background=PNL, foreground=INK,   font=("Segoe UI", 10))
        style.configure("Title.TLabel",    background=P,   foreground=INK,   font=("Segoe UI Semilight", 21))
        style.configure("Hero.TLabel",     background=P,   foreground=INK,   font=("Segoe UI Semilight", 32))
        style.configure("HeroSub.TLabel",  background=P,   foreground=MUTED, font=("Segoe UI", 11))
        style.configure("Subtitle.TLabel", background=P,   foreground=MUTED, font=("Segoe UI", 10))
        style.configure("Eyebrow.TLabel",  background=PNL, foreground=C["blue_500"], font=("Segoe UI", 7, "bold"))
        style.configure("PanelTitle.TLabel", background=PNL, foreground=INK, font=("Segoe UI Semilight", 14))
        style.configure("Help.TLabel",     background=PNL, foreground=MUTED, font=("Segoe UI", 9))
        style.configure("Status.TLabel",   background=P,   foreground=MUTED, font=("Segoe UI", 9))
        style.configure("CardTitle.TLabel",background=PNL, foreground=INK,   font=("Segoe UI", 12))
        style.configure("CardText.TLabel", background=PNL, foreground=MUTED, font=("Segoe UI", 9))
        style.configure("Notice.TLabel",   background=C["blue_100"], foreground=C["blue_800"], font=("Segoe UI", 9))

        # ── Inputs ──
        style.configure("TEntry", padding=8, fieldbackground=FIELD,
                        bordercolor=LINE, lightcolor=LINE, darkcolor=LINE,
                        foreground=INK, font=("Segoe UI", 10))
        style.map("TEntry", bordercolor=[("focus", C["blue_500"])])
        style.configure("TCombobox", padding=7, fieldbackground=FIELD,
                        bordercolor=LINE, arrowcolor=C["blue_600"], font=("Segoe UI", 10))
        style.map("TCombobox",
                  fieldbackground=[("readonly", FIELD)],
                  bordercolor=[("focus", C["blue_500"])])
        style.configure("TSpinbox", padding=7, fieldbackground=FIELD,
                        bordercolor=LINE, arrowcolor=C["blue_600"], font=("Segoe UI", 10))
        style.configure("TCheckbutton", background=PNL, foreground=INK,
                        font=("Segoe UI", 10), focuscolor=PNL,
                        indicatorbackground=C["white"], indicatorforeground=C["white"],
                        indicatormargin=(0, 0, 8, 0), padding=(0, 3))
        style.map("TCheckbutton",
                  background=[("active", PNL)],
                  indicatorbackground=[("selected", C["blue_700"]),
                                       ("active", C["blue_050"]),
                                       ("!selected", C["white"])],
                  indicatorforeground=[("selected", C["white"])],
                  bordercolor=[("!selected", LINE), ("selected", C["blue_700"])])
        style.configure("TRadiobutton", background=PNL, foreground=INK,
                        font=("Segoe UI", 10), focuscolor=PNL,
                        indicatorbackground=C["white"],
                        indicatormargin=(0, 0, 8, 0), padding=(0, 3))
        style.map("TRadiobutton",
                  background=[("active", PNL)],
                  indicatorbackground=[("selected", C["blue_700"]),
                                       ("active", C["blue_050"]),
                                       ("!selected", C["white"])],
                  bordercolor=[("!selected", LINE), ("selected", C["blue_700"])])

        # ── Buttons ──
        style.configure("TButton", padding=(12, 8), font=("Segoe UI", 9),
                        background=C["blue_050"], foreground=C["blue_800"],
                        borderwidth=1, bordercolor=LINE, relief="flat")
        style.map("TButton", background=[("active", C["blue_100"])])

        style.configure("Primary.TButton",
                        background=ACC, foreground=C["white"],
                        borderwidth=0, padding=(16, 10), font=("Segoe UI", 10))
        style.map("Primary.TButton",
                  background=[("active", C["blue_600"]), ("pressed", ACC_D)])

        style.configure("Quiet.TButton",
                        background=C["white"], foreground=C["blue_700"],
                        borderwidth=1, bordercolor=LINE,
                        padding=(11, 7), font=("Segoe UI", 9), relief="flat")
        style.map("Quiet.TButton",
                  background=[("active", C["blue_050"])],
                  bordercolor=[("active", C["blue_300"])])

        style.configure("Compact.TButton",
                        background=C["white"], foreground=C["blue_700"],
                        borderwidth=1, bordercolor=LINE,
                        padding=(6, 3), font=("Segoe UI", 8), relief="flat")
        style.map("Compact.TButton",
                  background=[("active", C["blue_050"])],
                  bordercolor=[("active", C["blue_300"])])

        style.configure("Round.TButton",
                        background=C["blue_050"], foreground=C["blue_700"],
                        borderwidth=1, bordercolor=LINE, padding=(9, 7),
                        font=("Segoe UI", 10), relief="flat")
        style.map("Round.TButton", background=[("active", C["blue_100"])])

        style.configure("Horizontal.TProgressbar",
                        troughcolor=C["blue_050"], background=C["blue_500"],
                        borderwidth=0, lightcolor=C["blue_500"], darkcolor=C["blue_500"])
        style.configure("TNotebook", background=PNL, borderwidth=0, tabmargins=(0, 0, 0, 0))
        style.configure(
            "TNotebook.Tab", background=C["blue_100"], foreground=C["blue_800"],
            padding=(14, 9), font=("Segoe UI", 9, "bold"), borderwidth=0
        )
        style.map(
            "TNotebook.Tab",
            background=[("selected", C["blue_700"]), ("active", C["blue_200"])],
            foreground=[("selected", C["white"]), ("active", C["blue_900"])]
        )
        style.configure(
            "Redact.Treeview", background=C["white"], fieldbackground=C["white"],
            foreground=INK, rowheight=25, font=("Segoe UI", 8), borderwidth=0
        )
        style.configure(
            "Redact.Treeview.Heading", background=C["blue_700"], foreground=C["white"],
            font=("Segoe UI", 8, "bold"), relief="flat", padding=(4, 6)
        )
        style.map("Redact.Treeview", background=[("selected", C["blue_200"])],
                  foreground=[("selected", C["blue_900"])])
        style.configure(
            "Compiler.Treeview", background=C["white"], fieldbackground=C["white"],
            foreground=INK, rowheight=25, font=("Segoe UI", 8), borderwidth=0
        )
        style.configure(
            "Compiler.Treeview.Heading", background=C["blue_700"], foreground=C["white"],
            font=("Segoe UI", 8, "bold"), relief="flat", padding=(4, 6)
        )
        style.map(
            "Compiler.Treeview", background=[("selected", C["blue_200"])],
            foreground=[("selected", C["blue_900"])]
        )
        style.configure("TPanedwindow", background=P)
        # Scrollbars must be unmistakably visible: a strong blue thumb on a
        # tinted trough, wider than the ttk default, with no vanishing states.
        for orient in ("Vertical", "Horizontal"):
            style.configure(
                f"{orient}.TScrollbar",
                background=C["blue_500"],          # the draggable thumb
                troughcolor=C["blue_100"],         # the track behind it
                bordercolor=C["blue_300"],
                lightcolor=C["blue_500"],
                darkcolor=C["blue_500"],
                arrowcolor=C["white"],
                gripcount=0,
                width=15,
                arrowsize=15,
                relief="flat",
            )
            style.map(
                f"{orient}.TScrollbar",
                background=[("active", C["blue_700"]),
                            ("pressed", C["blue_800"]),
                            ("disabled", C["blue_300"])],
                troughcolor=[("active", C["blue_100"])],
            )

    def _on_close(self):
        """Remove any temporary preview files before shutting down."""
        for page in getattr(self, "pages", {}).values():
            temporary = getattr(page, "_preview_temp", None)
            if temporary:
                try:
                    Path(temporary).unlink(missing_ok=True)
                except Exception:
                    pass
        self.destroy()

    def _apply_logos(self, height: int):
        """Load both logos at the requested pixel height and keep references."""
        self._logo_left = load_logo("left", height)
        self._logo_right = load_logo("right", height)
        if self._logo_left is not None:
            self.logo_left_label.configure(image=self._logo_left, text="")
        else:
            self.logo_left_label.configure(
                text="Tax-O-Smart", fg=COLORS["blue_900"],
                font=("Segoe UI Semilight", 16),
            )
        if self._logo_right is not None:
            self.logo_right_label.configure(image=self._logo_right, text="")
        else:
            self.logo_right_label.configure(text="")

    # Breakpoints: (minimum window width, scale factor, name)
    BREAKPOINTS = (
        (1600, 1.15, "large"),
        (1360, 1.00, "medium"),
        (1150, 0.92, "compact"),
        (0,    0.85, "small"),
    )

    def _scale_for_width(self, width: int):
        for minimum, factor, name in self.BREAKPOINTS:
            if width >= minimum:
                return factor, name
        return 0.85, "small"

    def _on_resize(self, event=None):
        """Re-scale fonts, icons, logos and the sidebar to the window size."""
        if event is not None and getattr(event, "widget", None) is not self:
            return
        width = self.winfo_width()
        if width < 200:
            return
        factor, name = self._scale_for_width(width)
        if name == getattr(self, "_layout_name", None):
            return
        self._layout_name = name
        self._layout_scale = factor

        def sz(base):
            return max(7, round(base * factor))

        self._apply_logos(sz(44))
        try:
            self.brand_title.configure(font=("Segoe UI Semilight", sz(15)))
            self.brand_sub.configure(font=("Segoe UI", sz(8)))
        except Exception:
            pass

        sidebar_width = round(248 * factor)
        try:
            self._sidebar_wrap.configure(width=sidebar_width + 1)
            self._sidebar_outer.configure(width=sidebar_width)
        except Exception:
            pass

        current = getattr(self, "_current_page", None)
        for key, button in self.nav_buttons.items():
            weight = "bold" if key == current else "normal"
            button.configure(
                font=("Segoe UI", sz(10), weight) if weight == "bold"
                else ("Segoe UI", sz(10)),
                pady=max(3, round(5 * factor)),
            )
        for label in getattr(self, "_nav_headings", []):
            try:
                label.configure(font=("Segoe UI", sz(7), "bold"))
            except Exception:
                pass
        try:
            self._logo_wordmark.configure(font=("Segoe UI Semilight", sz(16)))
            self._logo_tagline.configure(font=("Segoe UI", sz(7), "bold"))
        except Exception:
            pass

        style = ttk.Style(self)
        style.configure("TLabel", font=("Segoe UI", sz(10)))
        style.configure("Panel.TLabel", font=("Segoe UI", sz(10)))
        style.configure("Help.TLabel", font=("Segoe UI", sz(9)))
        style.configure("PanelTitle.TLabel", font=("Segoe UI Semilight", sz(14)))
        style.configure("Eyebrow.TLabel", font=("Segoe UI", sz(7), "bold"))
        style.configure("TButton", font=("Segoe UI", sz(9)))
        style.configure("Primary.TButton", font=("Segoe UI", sz(10)),
                        padding=(round(16 * factor), round(10 * factor)))
        style.configure("Quiet.TButton", font=("Segoe UI", sz(9)))
        style.configure("TEntry", padding=round(8 * factor))
        style.configure("TCombobox", padding=round(7 * factor))
        style.configure("TCheckbutton", font=("Segoe UI", sz(10)))
        style.configure("TRadiobutton", font=("Segoe UI", sz(10)))

        for page in self.pages.values():
            rewrap = getattr(page, "_rewrap_controls", None)
            if callable(rewrap):
                try:
                    rewrap()
                except Exception:
                    pass

    def show(self, key: str):
        self._current_page = key
        for page in self.pages.values():
            page.pack_forget()
        target = self.pages[key]
        target.pack(fill="both", expand=True)
        # A preview loaded while this page was hidden was drawn against a
        # zero-width canvas; redraw it now that real geometry exists.
        preview = getattr(target, "preview", None)
        if preview is not None and getattr(preview, "path", None):
            try:
                self.after(80, preview.render)
            except Exception:
                pass
        for nav_key, button in self.nav_buttons.items():
            if nav_key == key:
                button.configure(
                    bg=COLORS["blue_100"], fg=COLORS["blue_900"],
                    font=("Segoe UI", 10, "bold"),
                )
            else:
                button.configure(
                    bg=COLORS["white"], fg=COLORS["blue_800"],
                    font=("Segoe UI", 10),
                )


def main() -> int:
    try:
        app = SmartPDFPro()
        app.mainloop()
        return 0
    except tk.TclError as exc:
        print(f"Could not start the graphical interface: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
