"""Whether a file of the definition's open parts holds to its form (README.md, The open parts).

make parts-check runs it on export/parts.json, after comparing the file with what Lean gives:
python3 -I dev/parts-check.py <file> <version>. It checks that the file is an object of `version` and
`parts` alone, that `version` is the one given (flake.nix's), that every entry has the five keys and no
other, each a string but `uses`, a list of strings, that the entries are sorted by name and no two
share one, and that each entry's `uses` is sorted, leaves out its own name, and names entries alone.
It reads the file with Python's json, and changes nothing.
"""

import json
import sys

KEYS = {"name", "structure", "type", "doc", "uses"}


def faults(d, version):
    """The file's faults, each in a line; none where it holds to its form."""
    if not isinstance(d, dict) or set(d) != {"version", "parts"}:
        return ["the file is not an object of version and parts alone"]
    found = []
    if d["version"] != version:
        found.append(f"version is {d['version']!r}, flake.nix's is {version!r}")
    parts = d["parts"]
    if not isinstance(parts, list):
        return found + ["parts is not a list"]
    good = []
    for i, e in enumerate(parts):
        if not isinstance(e, dict) or set(e) != KEYS:
            found.append(f"entry {i} has not the five keys alone: {sorted(e) if isinstance(e, dict) else e!r}")
        elif not all(isinstance(e[k], str) for k in KEYS - {"uses"}):
            found.append(f"entry {i}: a key but uses is not a string")
        elif not isinstance(e["uses"], list) or not all(isinstance(u, str) for u in e["uses"]):
            found.append(f"entry {i} ({e['name']}): uses is not a list of strings")
        else:
            good.append(e)
    names = [e["name"] for e in good]
    if names != sorted(names):
        found.append("the entries are not sorted by name")
    seen = set()
    for n in names:
        if n in seen:
            found.append(f"two entries are named {n}")
        seen.add(n)
    for e in good:
        if e["uses"] != sorted(e["uses"]):
            found.append(f"{e['name']}: uses is not sorted")
        if e["name"] in e["uses"]:
            found.append(f"{e['name']} uses its own name")
        for u in e["uses"]:
            if u not in seen:
                found.append(f"{e['name']} uses {u}, which is no entry")
    return found


def main(argv):
    if len(argv) != 3:
        print("parts-check: python3 -I dev/parts-check.py <file> <version>")
        return 1
    path, version = argv[1], argv[2]
    with open(path, encoding="utf-8") as f:
        d = json.load(f)
    found = faults(d, version)
    for line in found:
        print(f"parts-check: {path}: {line}")
    if found:
        return 1
    print(f"parts-check: {path}: version {version}, {len(d['parts'])} entries, each of the five keys, "
          "sorted, no two of one name; each uses sorted, of other entries alone")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
