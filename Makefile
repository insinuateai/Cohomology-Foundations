# Cohomology Foundations Build System
# Fast incremental builds with parallel support

SHELL := /bin/bash
CORES := $(shell nproc 2>/dev/null || echo 4)

.PHONY: all fast full clean check watch lib timing profile slow-modules deps deps-png monitor \
        tmpfs-mount tmpfs-unmount tmpfs-status tmpfs-save tmpfs-restore \
        tmpfs-autosave tmpfs-autosave-disable tmpfs-autosave-status \
        axiom-count axiom-report axiom-list

# Default: fast incremental build (only modified modules)
all: fast

# Fast incremental build - ignores transitive deps, only rebuilds changed files
# Note: Lake handles parallelism automatically based on CPU cores
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
	@lake build Foundations --old

h1:
	@lake build H1Characterization --old

perspective:
	@lake build Perspective --old

infra:
	@lake build Infrastructure --old

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
	@lake build --old -v

# Print build stats
stats:
	@echo "Project Statistics:"
	@echo "  Lean files: $$(find . -name '*.lean' -not -path './.lake/*' | wc -l)"
	@echo "  Total lines: $$(find . -name '*.lean' -not -path './.lake/*' -exec cat {} + | wc -l)"
	@echo "  Lake cache: $$(du -sh .lake 2>/dev/null | cut -f1)"
	@echo "  CPU cores: $(CORES)"

# === Performance Profiling ===

# Timed build - measures total build duration
timing:
	@echo "Timing build..."
	@time lake build --old

# Profile build - shows per-module compilation (requires moreutils for ts)
profile:
	@echo "Build profile (time per module):"
	@if command -v ts >/dev/null 2>&1; then \
		lake build --old 2>&1 | ts -s "%.s"; \
	else \
		echo "Install moreutils for timestamps: sudo apt install moreutils"; \
		lake build --old; \
	fi

# Show modules being built (identifies what needs recompilation)
slow-modules:
	@echo "Modules requiring compilation:"
	@lake build --old 2>&1 | grep -E "Building|Compiling" | head -30 || echo "✓ All cached"

# === Dependency Analysis ===

# Generate import dependency graph (DOT format)
deps:
	@echo "Generating dependency graph..."
	@lake exe importGraph --to deps.dot 2>/dev/null || echo "Run 'lake build importGraph' first"
	@test -f deps.dot && echo "Graph saved to deps.dot" || true

# Convert DOT to PNG (requires graphviz)
deps-png: deps
	@if command -v dot >/dev/null 2>&1; then \
		dot -Tpng deps.dot -o deps.png && echo "PNG saved to deps.png"; \
	else \
		echo "Install graphviz: sudo apt install graphviz"; \
	fi

# === Resource Monitoring ===

# Build with detailed resource usage (shows CPU, memory, I/O stats)
monitor:
	@echo "Building with resource monitoring..."
	@/usr/bin/time -v lake build --old 2>&1 | tail -25

# === RAM Disk (tmpfs) for faster I/O ===
# Mounts .lake/build in RAM - preserves Mathlib cache on disk
# Current build size: ~83MB, tmpfs allocated: 256MB

TMPFS_SIZE := 256M
TMPFS_PATH := $(CURDIR)/.lake/build
TMPFS_BACKUP := $(CURDIR)/.lake/build-backup

# Mount tmpfs for .lake/build (requires sudo)
tmpfs-mount:
	@if mountpoint -q $(TMPFS_PATH) 2>/dev/null; then \
		echo "tmpfs already mounted at $(TMPFS_PATH)"; \
	else \
		echo "Mounting tmpfs ($(TMPFS_SIZE)) at .lake/build..."; \
		if [ -d $(TMPFS_PATH) ] && [ "$$(ls -A $(TMPFS_PATH) 2>/dev/null)" ]; then \
			echo "Backing up existing build cache..."; \
			rm -rf $(TMPFS_BACKUP) && cp -a $(TMPFS_PATH) $(TMPFS_BACKUP); \
		fi; \
		mkdir -p $(TMPFS_PATH); \
		sudo mount -t tmpfs -o size=$(TMPFS_SIZE) tmpfs $(TMPFS_PATH); \
		if [ -d $(TMPFS_BACKUP) ]; then \
			echo "Restoring build cache to tmpfs..."; \
			cp -a $(TMPFS_BACKUP)/* $(TMPFS_PATH)/ 2>/dev/null || true; \
		fi; \
		echo "✓ tmpfs mounted. Build artifacts now in RAM."; \
	fi

# Unmount tmpfs (optionally saves cache first)
tmpfs-unmount:
	@if mountpoint -q $(TMPFS_PATH) 2>/dev/null; then \
		echo "Saving build cache before unmount..."; \
		rm -rf $(TMPFS_BACKUP) && cp -a $(TMPFS_PATH) $(TMPFS_BACKUP); \
		sudo umount $(TMPFS_PATH); \
		mv $(TMPFS_BACKUP) $(TMPFS_PATH); \
		echo "✓ tmpfs unmounted. Cache preserved on disk."; \
	else \
		echo "tmpfs not mounted at $(TMPFS_PATH)"; \
	fi

# Check tmpfs status
tmpfs-status:
	@echo "=== tmpfs Status ==="
	@if mountpoint -q $(TMPFS_PATH) 2>/dev/null; then \
		echo "Status: MOUNTED (RAM disk active)"; \
		df -h $(TMPFS_PATH) | tail -1 | awk '{print "Size: " $$2 ", Used: " $$3 ", Avail: " $$4}'; \
	else \
		echo "Status: NOT MOUNTED (using disk)"; \
	fi
	@echo "Build cache size: $$(du -sh $(TMPFS_PATH) 2>/dev/null | cut -f1 || echo 'N/A')"

# Save tmpfs contents to disk backup
tmpfs-save:
	@if mountpoint -q $(TMPFS_PATH) 2>/dev/null; then \
		echo "Saving tmpfs contents to disk..."; \
		rm -rf $(TMPFS_BACKUP) && cp -a $(TMPFS_PATH) $(TMPFS_BACKUP); \
		echo "✓ Saved to .lake/build-backup"; \
	else \
		echo "tmpfs not mounted - nothing to save"; \
	fi

# Restore backup to tmpfs
tmpfs-restore:
	@if [ -d $(TMPFS_BACKUP) ]; then \
		if mountpoint -q $(TMPFS_PATH) 2>/dev/null; then \
			echo "Restoring backup to tmpfs..."; \
			cp -a $(TMPFS_BACKUP)/* $(TMPFS_PATH)/ 2>/dev/null || true; \
			echo "✓ Restored from .lake/build-backup"; \
		else \
			echo "tmpfs not mounted. Run 'make tmpfs-mount' first."; \
		fi; \
	else \
		echo "No backup found at .lake/build-backup"; \
	fi

# Auto-save tmpfs every 10 minutes (background loop)
tmpfs-autosave:
	@if [ -f /tmp/tmpfs-autosave.pid ] && kill -0 $$(cat /tmp/tmpfs-autosave.pid) 2>/dev/null; then \
		echo "Auto-save already running (PID $$(cat /tmp/tmpfs-autosave.pid))"; \
	else \
		echo "Starting auto-save (every 10 min)..."; \
		(while true; do sleep 600; cd $(CURDIR) && make tmpfs-save >/dev/null 2>&1; done) & \
		echo $$! > /tmp/tmpfs-autosave.pid; \
		echo "✓ Auto-save running in background (PID $$!)"; \
	fi

tmpfs-autosave-disable:
	@if [ -f /tmp/tmpfs-autosave.pid ]; then \
		kill $$(cat /tmp/tmpfs-autosave.pid) 2>/dev/null && rm /tmp/tmpfs-autosave.pid; \
		echo "✓ Auto-save stopped"; \
	else \
		echo "Auto-save not running"; \
	fi

tmpfs-autosave-status:
	@if [ -f /tmp/tmpfs-autosave.pid ] && kill -0 $$(cat /tmp/tmpfs-autosave.pid) 2>/dev/null; then \
		echo "Auto-save: RUNNING (PID $$(cat /tmp/tmpfs-autosave.pid))"; \
	else \
		echo "Auto-save: NOT RUNNING"; \
	fi

# === Axiom Tracking ===

# Quick axiom count by directory
axiom-count:
	@echo "=== Axiom Count by Directory ==="
	@for dir in Perspective MultiAgent Theories Infrastructure H1Characterization Foundations; do \
		if [ -d $$dir ]; then \
			count=$$(grep -rc "^axiom " $$dir --include="*.lean" 2>/dev/null | awk -F: '{sum+=$$2} END {print sum+0}'); \
			printf "  %-20s %3d\n" "$$dir/" "$$count"; \
		fi; \
	done
	@echo "  ────────────────────────"
	@printf "  %-20s %3d\n" "TOTAL" "$$(grep -rc '^axiom ' . --include='*.lean' | grep -v '\.lake' | awk -F: '{sum+=$$2} END {print sum}')"

# Full axiom report to .claude/axiom-report.md
axiom-report:
	@./scripts/axiom-report.sh

# Quick axiom list with files
axiom-list:
	@grep -rn "^axiom " . --include="*.lean" | grep -v "\.lake" | \
		sed 's/:axiom /:  /' | sort

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
	@echo "Profiling targets:"
	@echo "  timing     - Timed build with total duration"
	@echo "  profile    - Per-module timing (needs moreutils)"
	@echo "  slow-modules - Show modules being compiled"
	@echo "  monitor    - Build with CPU/memory stats"
	@echo ""
	@echo "RAM disk (tmpfs) - faster I/O:"
	@echo "  tmpfs-mount   - Mount .lake/build in RAM (needs sudo)"
	@echo "  tmpfs-unmount - Unmount and save to disk"
	@echo "  tmpfs-status  - Check if tmpfs is active"
	@echo "  tmpfs-save    - Save RAM contents to disk backup"
	@echo "  tmpfs-restore - Restore backup to RAM"
	@echo "  tmpfs-autosave - Start auto-save (every 10 min)"
	@echo "  tmpfs-autosave-status - Check if auto-save running"
	@echo ""
	@echo "Dependency analysis:"
	@echo "  deps       - Generate import graph (deps.dot)"
	@echo "  deps-png   - Convert to PNG (needs graphviz)"
	@echo ""
	@echo "Axiom tracking:"
	@echo "  axiom-count  - Count axioms by directory"
	@echo "  axiom-report - Generate full report (.claude/axiom-report.md)"
	@echo "  axiom-list   - List all axioms with locations"
	@echo ""
	@echo "Library targets:"
	@echo "  foundations, h1, perspective, infra"
