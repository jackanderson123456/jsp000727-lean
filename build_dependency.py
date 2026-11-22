"""Build the pinned Erdős 254 dependency one Lean module at a time."""

from pathlib import Path
import re
import subprocess


def main() -> None:
    project = Path(__file__).resolve().parent
    upstream = project / ".lake/packages/Research/starfleet/erdos-254"
    if not (upstream / "Research").is_dir():
        raise SystemExit("Fetch the package first with lake exe cache get.")

    visited: set[str] = set()

    def imports(source: Path) -> list[str]:
        return re.findall(r"^import (Research\.\w+)\s*$", source.read_text(encoding="utf-8"), re.M)

    def build(module: str) -> None:
        if module in visited:
            return
        visited.add(module)
        path = Path(*module.split("."))
        for dependency in imports(upstream / path.with_suffix(".lean")):
            build(dependency)
        olean = upstream / ".lake/build/lib/lean" / path.with_suffix(".olean")
        if not olean.exists():
            subprocess.run(["lake", "build", module], cwd=project, check=True)

    for source in sorted(project.glob("*.lean")):
        for module in imports(source):
            build(module)


if __name__ == "__main__":
    main()
