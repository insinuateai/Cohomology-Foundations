#!/bin/bash
# Axiom Dependency Report Generator
# Usage: ./scripts/axiom-report.sh [--json]
#
# Generates .claude/axiom-report.md with:
# - Axiom count by directory
# - Full list with file:line references
# - Usage analysis (which files reference each axiom)

set -e

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUTPUT_FILE="$PROJECT_ROOT/.claude/axiom-report.md"

# Colors for terminal output (disabled if piping)
if [ -t 1 ]; then
    RED='\033[0;31m'
    GREEN='\033[0;32m'
    YELLOW='\033[1;33m'
    NC='\033[0m'
else
    RED='' GREEN='' YELLOW='' NC=''
fi

# Count axioms by directory
count_by_dir() {
    for dir in Perspective MultiAgent Theories Infrastructure H1Characterization Foundations; do
        if [ -d "$PROJECT_ROOT/$dir" ]; then
            count=$(grep -rc "^axiom " "$PROJECT_ROOT/$dir" --include="*.lean" 2>/dev/null | awk -F: '{sum+=$2} END {print sum+0}')
            printf "  %-20s %3d\n" "$dir/" "$count"
        fi
    done
}

# Get total axiom count
total_count() {
    grep -rc "^axiom " "$PROJECT_ROOT" --include="*.lean" 2>/dev/null | grep -v "\.lake" | awk -F: '{sum+=$2} END {print sum}'
}

# Extract all axioms with file:line:name
extract_axioms() {
    grep -rn "^axiom " "$PROJECT_ROOT" --include="*.lean" 2>/dev/null | grep -v "\.lake" | while IFS=: read -r file line content; do
        # Get axiom name (first word after "axiom ")
        name=$(echo "$content" | sed 's/^axiom \([^ ({:]*\).*/\1/')
        # Make path relative
        relpath="${file#$PROJECT_ROOT/}"
        echo "$relpath:$line:$name"
    done | sort
}

# Find files that use a given axiom (excluding its definition)
find_usages() {
    local axiom_name="$1"
    local def_file="$2"
    grep -rln "\b$axiom_name\b" "$PROJECT_ROOT" --include="*.lean" 2>/dev/null | \
        grep -v "\.lake" | \
        grep -v "$def_file" | \
        sed "s|$PROJECT_ROOT/||g" | \
        head -5
}

# Generate markdown report
generate_report() {
    local total=$(total_count)

    cat << EOF
# Axiom Dependency Report

Generated: $(date -Iseconds)
Total axioms: $total
Target: ~15 external math axioms

## Summary by Directory

| Directory | Count | % of Total |
|-----------|-------|------------|
EOF

    for dir in Perspective MultiAgent Theories Infrastructure H1Characterization Foundations; do
        if [ -d "$PROJECT_ROOT/$dir" ]; then
            count=$(grep -rc "^axiom " "$PROJECT_ROOT/$dir" --include="*.lean" 2>/dev/null | awk -F: '{sum+=$2} END {print sum+0}')
            if [ "$count" -gt 0 ]; then
                pct=$((count * 100 / total))
                printf "| %-20s | %3d | %3d%% |\n" "$dir/" "$count" "$pct"
            fi
        fi
    done

    cat << EOF

## All Axioms

| File | Line | Axiom Name |
|------|------|------------|
EOF

    extract_axioms | while IFS=: read -r file line name; do
        printf "| \`%s\` | %s | \`%s\` |\n" "$file" "$line" "$name"
    done

    cat << EOF

## Files with Most Axioms

EOF

    grep -rc "^axiom " "$PROJECT_ROOT" --include="*.lean" 2>/dev/null | \
        grep -v "\.lake" | \
        grep -v ":0$" | \
        sort -t: -k2 -rn | \
        head -10 | \
        while IFS=: read -r file count; do
            relpath="${file#$PROJECT_ROOT/}"
            echo "- \`$relpath\`: $count axioms"
        done

    cat << EOF

## Quick Actions

Run these commands to work with axioms:

\`\`\`bash
# Count axioms
make axiom-count

# Regenerate this report
make axiom-report

# List axioms in a specific file
grep -n "^axiom " Perspective/SpectralGap.lean

# Find usages of an axiom
grep -rln "axiom_name" . --include="*.lean" | grep -v .lake
\`\`\`

## Notes

- Axioms marked with \`-- KEEP\` are external math results (spectral theory, etc.)
- See \`.claude/axiom-registry.md\` for full signatures and elimination status
- Priority: self-contained files with Mathlib-only imports
EOF
}

# Main
case "${1:-}" in
    --count)
        echo "Axiom count by directory:"
        count_by_dir
        echo "  ──────────────────────"
        printf "  %-20s %3d\n" "TOTAL" "$(total_count)"
        ;;
    --list)
        extract_axioms
        ;;
    *)
        echo "Generating axiom report..."
        mkdir -p "$(dirname "$OUTPUT_FILE")"
        generate_report > "$OUTPUT_FILE"
        echo "Report written to $OUTPUT_FILE"
        echo ""
        echo "Summary:"
        count_by_dir
        echo "  ──────────────────────"
        printf "  %-20s %3d\n" "TOTAL" "$(total_count)"
        ;;
esac
