from bs4 import BeautifulSoup
import sys

def crop_svg_bottom(svg_in, svg_out, crop_from_bottom):
    with open(svg_in, "r", encoding="utf-8") as f:
        svg_soup = BeautifulSoup(f.read(), "xml")

    svg_tag = svg_soup.find("svg")
    if not svg_tag:
        print("SVG not found!")
        sys.exit(1)

    if 'viewBox' in svg_tag.attrs:
        vb = svg_tag['viewBox'].split()
        if len(vb) == 4:
            x, y, w, h = map(float, vb)
            # Insert as first element
            rect = svg_soup.new_tag("rect", x=x, y=y, width=w, height=h, fill="white")
            svg_tag.insert(0, rect)
        x, y, w, h = float(vb[0]), float(vb[1]), float(vb[2]), float(vb[3])
        new_height = h - crop_from_bottom
        if new_height <= 0:
            print(f"Crop amount {crop_from_bottom} is too large for SVG of height {h}")
            sys.exit(1)
        svg_tag['viewBox'] = f"{x} {y} {w} {new_height}"
        if 'height' in svg_tag.attrs:
            svg_tag['height'] = str(new_height)

        # Remove all elements with y attribute below new_height
        for text in svg_soup.find_all("text"):
            try:
                yval = float(text.get("y", "0"))
                if yval > new_height:
                    text.decompose()
            except Exception:
                pass

        print(f"Cropped {crop_from_bottom} from bottom. New SVG height: {new_height}")
    else:
        print("No viewBox found, cannot crop.")
        sys.exit(1)

    with open(svg_out, "w", encoding="utf-8") as f:
        f.write(str(svg_soup))

if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: python crop_svg_bottom.py input.svg output.svg crop_from_bottom")
        sys.exit(1)
    crop_svg_bottom(sys.argv[1], sys.argv[2], float(sys.argv[3]))
