#!/usr/bin/env bash
# Build the Verso textbook and serve it locally.
# Usage:
#   ./serve.sh            # build + serve on port 8000
#   PORT=9000 ./serve.sh  # use a custom port
#   ./serve.sh --output ../docs  # pass extra args to generate-doc

set -euo pipefail

PORT=${PORT:-8000}

echo "Building documentation..."
lake exe generate-doc "$@"

echo ""
echo "Serving at http://localhost:${PORT}  (Ctrl-C to stop)"
python3 -m http.server "$PORT" --directory _out
