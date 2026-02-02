#!/bin/bash
# Quick status for session start

cd /workspaces/Cohomology-Foundations

# Use make targets if available (more accurate)
SORRIES=$(grep -rE "^\s*sorry\b|:= sorry\b" --include="*.lean" 2>/dev/null | grep -v "^Binary" | wc -l | tr -d ' ')
AXIOMS=$(make axiom-count 2>/dev/null | grep "TOTAL" | awk '{print $2}' || grep -rE "^axiom\s+" --include="*.lean" 2>/dev/null | wc -l)
SKILL_LINES=$(wc -l < .claude/skill-document.md 2>/dev/null | tr -d ' ')

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 Sorries: $SORRIES | Axioms: $AXIOMS"
echo "📄 skill-document.md: $SKILL_LINES/100 lines"
if [ "$SKILL_LINES" -gt 100 ] 2>/dev/null; then
  echo "⚠️  Compress skill-document.md!"
fi
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
