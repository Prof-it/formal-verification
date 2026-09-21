## How to Convert Mermaid (.mmd) Diagrams to PNG on macOS

This directory contains various Mermaid diagram files (`*.mmd`). To convert them to PNG image format via the command line (CLI) on macOS, use the excellent [Mermaid CLI (`mmdc`)](https://github.com/mermaid-js/mermaid-cli) tool.

### 1. Install Mermaid CLI

You must have [Node.js](https://nodejs.org/) installed. Then run:

```sh
npm install -g @mermaid-js/mermaid-cli
```

### 2. Convert `.mmd` to `.png`

Navigate to this `images` directory in your terminal and run:

```sh
mmdc -i agentic-loop-nasa.mmd -o agentic-loop-nasa.png
```

Or to convert all `.mmd` files in the directory:

```sh
for f in *.mmd; do mmdc -i "$f" -o "${f%.mmd}.png"; done
```

This will create PNG images with corresponding names for each Mermaid file.
### 2b. High-Resolution (Retina) PNG Output

To produce higher-resolution PNGs, use a Puppeteer config that sets a high `deviceScaleFactor` (e.g. `2` for Retina):

1. Create a file named `puppeteer-retina-config.json` in this directory with the following contents:
   ```json
   {
     "defaultViewport": {
       "width": 800,
       "height": 600,
       "deviceScaleFactor": 2
     }
   }

### 3. Additional Tips

- You can also output to SVG format with `-o yourfile.svg`.
- For Retina/high-res, use `--puppeteerConfigFile` to specify device scale.
- For more options and troubleshooting, see the [official mermaid-cli documentation](https://github.com/mermaid-js/mermaid-cli#usage).

---

**Tip:** If you change any `.mmd` file, regenerate the `.png` before including it in your paper/report!