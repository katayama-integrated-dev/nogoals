#!/usr/bin/env python3
"""Regenerate the site's raster assets from assets/images/source/contours.jpg.

    ./scripts/make-images.py <product name>      (from the site root)

  logo.png  the mark: a turnstile (the "proves" sign), name-independent
  hero.jpg  the home hero background: a wide band, never upscaled
  card.jpg  the 1200x630 social card

The card's headline and tagline are typed here as well as in Site/Blocks.lean
and Site/Pages.lean: change them in both. macOS only (Helvetica Neue).
"""
import sys
from PIL import Image, ImageDraw, ImageFont

INK, SKY, TEXT, MUTED = (15, 23, 42), (125, 211, 252), (248, 250, 252), (148, 163, 184)
product = sys.argv[1]
raw = Image.open("assets/images/source/contours.jpg").convert("RGB")

# Re-seat the drawing on the site's exact background: keep only what is
# brighter than the source's own background and add it to INK, so the image
# has no visible edge against the page.
base = raw.getpixel((8, 8))
src = Image.merge("RGB", [
    ch.point(lambda v, b=b, i=i: min(255, i + max(0, v - b)))
    for ch, b, i in zip(raw.split(), base, INK)])
w, h = src.size

S = 256
logo = Image.new("RGBA", (S, S), (0, 0, 0, 0))
d = ImageDraw.Draw(logo)
d.rounded_rectangle([0, 0, S - 1, S - 1], radius=56, fill=INK)
d.rounded_rectangle([76, 60, 100, 196], radius=8, fill=SKY)
d.rounded_rectangle([76, 116, 190, 140], radius=8, fill=SKY)
logo.resize((128, 128), Image.LANCZOS).save("assets/images/logo.png", optimize=True)

band = int(w * 0.36)
src.crop((0, (h - band) // 2, w, (h + band) // 2)).save(
    "assets/images/hero.jpg", quality=78, optimize=True, progressive=True)

ch = int(w * 630 / 1200)
card = src.crop((0, (h - ch) // 2, w, (h - ch) // 2 + ch)).resize((1200, 630), Image.LANCZOS)
d = ImageDraw.Draw(card)
def font(size, bold=False):
    return ImageFont.truetype("/System/Library/Fonts/HelveticaNeue.ttc", size, index=1 if bold else 0)
d.text((80, 200), "Broken websites", font=font(76, True), fill=TEXT)
d.text((80, 290), "don't build.", font=font(76, True), fill=TEXT)
d.text((82, 410), f"{product} — a static site generator in Lean 4", font=font(30), fill=MUTED)
card.save("assets/images/card.jpg", quality=82, optimize=True, progressive=True)
print("logo.png hero.jpg card.jpg written")
