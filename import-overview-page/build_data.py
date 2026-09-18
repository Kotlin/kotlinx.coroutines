#!/usr/bin/env python3
"""Build the script-loadable overview catalog using only the Python stdlib."""

import json
from pathlib import Path
import re


def collect_data(source_root):
    """Read evidence without modifying it or depending on the working directory."""
    source_root = Path(source_root)
    if not source_root.is_dir():
        raise NotADirectoryError(source_root)

    documents = []
    files = []
    catalogs = {}
    paths = sorted(
        (path for path in source_root.rglob("*") if path.is_file()),
        key=lambda path: path.relative_to(source_root).as_posix(),
    )
    for path in paths:
        relative_path = path.relative_to(source_root)
        files.append({"path": relative_path.as_posix(), "size_bytes": path.stat().st_size})
        if path.suffix.lower() == ".md":
            # Decoding bytes avoids universal-newline translation of original evidence.
            markdown = path.read_bytes().decode("utf-8")
            heading = re.search(r"^ {0,3}#[ \t]+([^\r\n]*)", markdown, re.MULTILINE)
            title = re.sub(r"[ \t]+#+[ \t]*$", "", heading.group(1)).strip() if heading else path.stem
            documents.append({"path": relative_path.as_posix(), "title": title, "markdown": markdown})
        if relative_path.parent == Path("bin") and path.suffix == ".json":
            catalogs[path.stem] = json.loads(path.read_bytes().decode("utf-8"))

    return {"documents": documents, "files": files, "json": catalogs, "source": "../import-overview/"}


def write_data(data, output):
    """Write deterministic JavaScript that also works when loaded over file://."""
    payload = json.dumps(data, ensure_ascii=False, sort_keys=True, indent=2, allow_nan=False)
    payload = payload.replace("<", "\\u003c").replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")
    Path(output).write_bytes(("window.IMPORT_OVERVIEW = " + payload + ";\n").encode("utf-8"))


if __name__ == "__main__":
    page_root = Path(__file__).resolve().parent
    write_data(collect_data(page_root.parent / "import-overview"), page_root / "data.js")