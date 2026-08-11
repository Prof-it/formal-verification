from bs4 import BeautifulSoup
import sys

def crop_svg_bottom(svg_in, svg_out, new_height):
    with open(svg_in, "r", encoding="utf-8") as f:
        svg_soup = BeautifulSoup(f.read(), "xml")

    svg_tag = svg_soup.find("svg")
    if not svg_tag:
        print("SVG not found!")
        sys.exit(1)

    if 'viewBox' in svg_tag.attrs:
        vb = svg_tag['viewBox'].split()
        x, y, w, h = float(vb[0]), float(vb[1]), float(vb[2]), float(vb[3])
        if new_height >= h:
            print(f"New height must be less than original SVG height of {h}")
            sys.exit(1)
        svg_tag['viewBox'] = f"{x} {y} {w} {new_height}"
        if 'height' in svg_tag.attrs:
            svg_tag['height'] = str(new_height)

    # Optionally: Remove all elements with y attribute below the new height
    for text in svg_soup.find_all("text"):
        try:
            yval = float(text.get("y", "0"))
            if yval > new_height:
                text.decompose()
        except Exception:
            pass
    # You could optionally remove lines/paths too, but it's rarely needed for Gantt axis cropping

    with open(svg_out, "w", encoding="utf-8") as f:
        f.write(str(svg_soup))

    print(f"Cropped SVG to new height {new_height}")

if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: python crop_svg_bottom.py input.svg output.svg new_height")
        sys.exit(1)
    crop_svg_bottom(sys.argv[1], sys.argv[2], float(sys.argv[3]))