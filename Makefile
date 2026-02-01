# Cohomology Foundations Build System
# Fast incremental builds with parallel support

SHELL := /bin/bash
CORES := $(shell nproc 2>/dev/null || echo 4)

.PHONY: all fast full clean check watch lib

# Default: fast incremental build (only modified modules)
all: fast

# Fast incremental build - ignores transitive deps, only rebuilds changed files
fast:
	@echo "Fast incremental build (--old flag)..."
	@lake build --old 2>&1 | grep -v "^⚠\|^warning:" || true

# Full rebuild with all transitive dependencies
full:
	@echo "Full build with all dependencies..."
	@time lake build

# Quiet build - minimal output
quiet:
	@lake build --old -q

# Check for errors only (no build output)
check:
	@lake build --old 2>&1 | grep -E "^error|sorry|axiom" || echo "✓ No errors found"

# Clean only project build artifacts (preserves Mathlib cache!)
clean:
	@echo "Cleaning project artifacts only (preserving Mathlib cache)..."
	@rm -rf .lake/build/lib/lean/{Foundations,H1Characterization,Perspective,MultiAgent,Infrastructure,H2Characterization,Experimental,Theories,DoubleSquaredZero}
	@rm -rf .lake/build/ir/{Foundations,H1Characterization,Perspective,MultiAgent,Infrastructure,H2Characterization,Experimental,Theories,DoubleSquaredZero}
	@echo "Done. Run 'make clean-all' to also clean Mathlib cache."

# Clean everything including Mathlib cache (SLOW to rebuild!)
clean-all:
	@echo "WARNING: This will require rebuilding Mathlib (can take hours)"
	lake clean

# Build specific libraries
foundations:
	lake build Foundations --old

h1:
	lake build H1Characterization --old

perspective:
	lake build Perspective --old

infra:
	lake build Infrastructure --old

# Watch mode for development (requires entr or fswatch)
watch:
	@if command -v fswatch >/dev/null 2>&1; then \
		echo "Watching for changes (Ctrl+C to stop)..."; \
		fswatch -o --event=Updated $$(find . -name '*.lean' -not -path './.lake/*') | xargs -n1 -I{} make fast; \
	elif command -v inotifywait >/dev/null 2>&1; then \
		echo "Watching for changes (Ctrl+C to stop)..."; \
		while inotifywait -e modify -r --include '\.lean$$' . 2>/dev/null; do make fast; done; \
	else \
		echo "Install fswatch or inotify-tools for watch mode"; \
		exit 1; \
	fi

# Verify no sorries or axioms
verify:
	@echo "Checking for sorries and axioms..."
	@grep -rn "sorry" --include="*.lean" . --exclude-dir=.lake | grep -v "-- sorry" | grep -v "^Binary" || echo "✓ No sorries"
	@grep -rn "^axiom" --include="*.lean" . --exclude-dir=.lake || echo "✓ No axioms"

# Build with verbose output for debugging
verbose:
	lake build --old -v

# Print build stats
stats:
	@echo "Project Statistics:"
	@echo "  Lean files: $$(find . -name '*.lean' -not -path './.lake/*' | wc -l)"
	@echo "  Total lines: $$(find . -name '*.lean' -not -path './.lake/*' -exec cat {} + | wc -l)"
	@echo "  Lake cache: $$(du -sh .lake 2>/dev/null | cut -f1)"

help:
	@echo "Available targets:"
	@echo "  fast       - Fast incremental build (default)"
	@echo "  full       - Full rebuild with all deps"
	@echo "  quiet      - Build with minimal output"
	@echo "  check      - Check for errors only"
	@echo "  clean      - Clean build artifacts"
	@echo "  watch      - Watch mode for development"
	@echo "  verify     - Check for sorries/axioms"
	@echo "  verbose    - Verbose build output"
	@echo "  stats      - Print project statistics"
	@echo ""
	@echo "Library targets:"
	@echo "  foundations, h1, perspective, infra"
