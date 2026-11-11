#!/usr/bin/env python3
"""Lightweight checks for tracked files; not a Lean parser or proof checker."""
from pathlib import Path
import re
import subprocess
from urllib.parse import unquote, urlsplit


def lean_code(source):
    """Blank comments and literals, preserving newlines and nested block comments."""
    out = []
    i, depth = 0, 0
    quoted = False
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if depth:
            if pair == "/-":
                depth += 1
                out.append("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif quoted:
            if char == "\\" and i + 1 < len(source):
                out.append(" \n" if source[i + 1] == "\n" else "  ")
                i += 2
            else:
                quoted = char != '"'
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            out.append(" " * (end - i))
            i = end
        elif char == "'" and (literal := re.match(r"'(?:\\.|[^'\\\n])'", source[i:])):
            out.append(" " * len(literal.group()))
            i += len(literal.group())
        elif char == '"':
            quoted = True
            out.append(" ")
            i += 1
        else:
            out.append(char)
            i += 1
    return "".join(out)


def markdown_prose(source):
    lines, fence = [], None
    for line in source.splitlines(keepends=True):
        marker = re.match(r"^\s*(`{3,}|~{3,})", line)
        if marker:
            token = marker.group(1)
            if fence is None:
                fence = token
            elif token[0] == fence[0] and len(token) >= len(fence):
                fence = None
            lines.append("\n")
        else:
            lines.append("\n" if fence else line)
    return re.sub(r"(`+).*?\1", "", "".join(lines))


def main():
    root = Path(__file__).resolve().parents[1]
    names = subprocess.check_output(
        ["git", "ls-files", "-z"], cwd=root).decode().split("\0")
    tracked = {name for name in names if name}
    errors = []
    modules = docs = links = 0
    for name in sorted(tracked):
        path = root / name
        if not path.is_file():
            errors.append(f"{name}: tracked file is missing")
            continue
        if name.endswith(".lean") and (
                name.startswith(("RamanujanWeil/", "scripts/audit/"))
                or name == "RamanujanWeil.lean"):
            modules += 1
            code = lean_code(path.read_text())
            for match in re.finditer(r"\b(sorry|admit|axiom|native_decide)\b", code):
                line = code.count("\n", 0, match.start()) + 1
                errors.append(f"{name}:{line}: forbidden proof token {match.group()}")
            for match in re.finditer(r"^\s*import\s+([^\n]+)", code, re.M):
                for module in match.group(1).split():
                    if module.startswith("RamanujanWeil."):
                        target = module.replace(".", "/") + ".lean"
                        if target not in tracked:
                            errors.append(f"{name}: project import is not tracked: {target}")
        elif name.endswith(".md"):
            docs += 1
            prose = markdown_prose(path.read_text())
            for match in re.finditer(r"\[[^\]\n]*\]\(([^\s)]+)\)", prose):
                target = match.group(1).strip("<>")
                url = urlsplit(target)
                if url.scheme or url.netloc or not url.path:
                    continue
                links += 1
                resolved = (path.parent / unquote(url.path)).resolve()
                try:
                    relative = resolved.relative_to(root).as_posix()
                except ValueError:
                    errors.append(f"{name}: link leaves the repository: {target}")
                    continue
                if not resolved.exists():
                    errors.append(f"{name}: broken local link: {target}")
                elif resolved.is_file() and relative not in tracked:
                    errors.append(f"{name}: link target is not tracked: {target}")
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"Passed: {modules} Lean source/audit files, {docs} Markdown files, "
          f"{links} local links; project imports and source hygiene checked.")
    print("This is a source/documentation check, not Lean proof verification.")


if __name__ == "__main__":
    main()
