"""Run with python3 -m unittest discover -s import-overview-page -v."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from build_data import collect_data, write_data


PAGE_ROOT = Path(__file__).resolve().parent


def read_payload(output):
    script = output.read_bytes().decode("utf-8")
    prefix = "window.IMPORT_OVERVIEW = "
    if not script.startswith(prefix) or not script.endswith(";\n"):
        raise AssertionError("Output must be a script-loadable window assignment")
    return json.loads(script[len(prefix):-2])


class BuildDataTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(dir=PAGE_ROOT)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "import-overview"
        self.source.mkdir()

    def put(self, path, content):
        target = self.source / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content.encode("utf-8") if isinstance(content, str) else content)
        return target

    def test_recursive_documents_and_all_file_sizes(self):
        originals = {
            "z/deep/guide.md": "## Not the title\r\n# First title\r\n\r\nCafé\r\n# Later title\r\n",
            "index.md": "# Index\n\nOriginal text without final newline",
            "bin/README.md": "# Evidence\n",
            "notes.MD": "# Uppercase extension\n",
            "no-heading.md": "Plain text\n",
        }
        for path, markdown in originals.items():
            self.put(path, markdown)
        self.put("bin/raw/deep/data.bin", b"\x00\xff\r\n")
        self.put(".hidden", b"hidden")
        self.put("bin/raw/nested.json", '{"raw": true}')
        before = {p.relative_to(self.source).as_posix(): p.read_bytes() for p in self.source.rglob("*") if p.is_file()}
        data = collect_data(self.source)
        self.assertEqual(data["source"], "../import-overview/")
        self.assertEqual([d["path"] for d in data["documents"]], sorted(originals))
        self.assertEqual({d["path"]: d["markdown"] for d in data["documents"]}, originals)
        titles = {d["path"]: d["title"] for d in data["documents"]}
        self.assertEqual(titles["z/deep/guide.md"], "First title")
        self.assertEqual(titles["no-heading.md"], "no-heading")
        self.assertEqual(data["files"], [{"path": p, "size_bytes": len(before[p])} for p in sorted(before)])
        self.assertEqual(data["json"], {})
        after = {p.relative_to(self.source).as_posix(): p.read_bytes() for p in self.source.rglob("*") if p.is_file()}
        self.assertEqual(before, after)

    def test_all_top_level_catalogs_preserve_null_times_and_metadata(self):
        catalogs = {
            "work-items": {"schema_version": 1, "items": [{"duration_ms": None}], "metadata": {"custom": [True, False, ""]}},
            "trace-analysis": {"startTime": 1758123456789012, "duration": 38660.125, "timestamp": "2026-09-18T12:36:00Z", "missing": None},
            "future-catalog": [{"arbitrary": {"nested": [None, 0, -1, 1.25]}}],
            "scalar": None,
        }
        for name, value in catalogs.items():
            self.put("bin/" + name + ".json", json.dumps(value))
        self.put("elsewhere.json", "null")
        self.put("bin/raw/not-a-catalog.json", "[]")
        data = collect_data(self.source)
        self.assertEqual(data["json"], catalogs)
        self.assertEqual(list(data["json"]), sorted(catalogs))
        output = self.root / "data.js"
        write_data(data, output)
        self.assertEqual(read_payload(output), data)

    def test_safe_embedding_round_trips_original_text(self):
        text = '# Title\n</script><script>alert("x")</script>\u2028\u2029\\u003c\n雪'
        self.put("index.md", text)
        self.put("bin/metadata.json", json.dumps({"<key>": text}))
        data = collect_data(self.source)
        output = self.root / "data.js"
        write_data(data, output)
        script = output.read_bytes().decode("utf-8")
        for unsafe in ("<", "\u2028", "\u2029"):
            self.assertNotIn(unsafe, script)
        for escaped in ("\\u003c", "\\u2028", "\\u2029"):
            self.assertIn(escaped, script)
        self.assertEqual(read_payload(output), data)

    def test_determinism_ignores_creation_and_mapping_order(self):
        self.put("z.md", "# Z\n")
        self.put("a.md", "# A\n")
        self.put("bin/z.json", '{"z": 1, "a": 2}')
        first = collect_data(self.source)
        output = self.root / "data.js"
        write_data(first, output)
        original = output.read_bytes()
        self.put("bin/z.json", '{"a": 2, "z": 1}')
        second = collect_data(self.source)
        self.assertEqual(first, second)
        write_data(dict(reversed(list(second.items()))), output)
        self.assertEqual(output.read_bytes(), original)

    def test_missing_root_and_malformed_catalog_fail(self):
        with self.assertRaises(NotADirectoryError):
            collect_data(self.root / "missing")
        self.put("bin/broken.json", "{")
        with self.assertRaises(json.JSONDecodeError):
            collect_data(self.source)

    def test_empty_source(self):
        self.assertEqual(collect_data(self.source), {
            "documents": [], "files": [], "json": {}, "source": "../import-overview/",
        })

    def test_main_is_independent_of_working_directory(self):
        self.put("index.md", "# Fixture\n")
        page = self.root / "import-overview-page"
        page.mkdir()
        builder = page / "build_data.py"
        builder.write_bytes((PAGE_ROOT / "build_data.py").read_bytes())
        result = subprocess.run([sys.executable, str(builder)], cwd=self.source, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(read_payload(page / "data.js"), collect_data(self.source))

    def test_actual_dataset_coverage_and_preservation(self):
        source = PAGE_ROOT.parent / "import-overview"
        data = collect_data(source)
        paths = sorted(
            (p for p in source.rglob("*") if p.is_file()),
            key=lambda p: p.relative_to(source).as_posix(),
        )
        self.assertTrue(paths)
        self.assertEqual(data["files"], [
            {"path": p.relative_to(source).as_posix(), "size_bytes": p.stat().st_size} for p in paths
        ])
        markdown_paths = [p for p in paths if p.suffix.lower() == ".md"]
        self.assertEqual([d["path"] for d in data["documents"]], [p.relative_to(source).as_posix() for p in markdown_paths])
        for document, path in zip(data["documents"], markdown_paths):
            self.assertEqual(document["markdown"].encode("utf-8"), path.read_bytes())
            self.assertTrue(document["title"])
        catalogs = {p.stem: json.loads(p.read_bytes().decode("utf-8")) for p in sorted((source / "bin").glob("*.json")) if p.is_file()}
        self.assertEqual(data["json"], catalogs)
        self.assertIn("work-items", catalogs)
        self.assertIn("trace-analysis", catalogs)
        self.assertTrue(any(p["path"].startswith("bin/traces/") for p in data["files"]))
        self.assertTrue(any(p["path"].startswith("bin/benchmarks/") for p in data["files"]))
        output = self.root / "data.js"
        write_data(data, output)
        self.assertEqual(read_payload(output), data)
        original = output.read_bytes()
        write_data(collect_data(source), output)
        self.assertEqual(output.read_bytes(), original)


if __name__ == "__main__":
    unittest.main()