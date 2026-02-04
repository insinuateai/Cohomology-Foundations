#!/bin/bash
# Quick status for session start

cd /workspaces/Cohomology-Foundations

# Use make targets if available (more accurate)
SORRIES=$(timeout 3 sh -c 'grep -rE "^\s*sorry\b|:= sorry\b" --include="*.lean" --exclude-dir=.lake --exclude-dir=.git 2>/dev/null | grep -v "^Binary" | wc -l | tr -d " "')
SORRY_STATUS=$?
if [ "$SORRY_STATUS" -eq 124 ]; then
  SORRIES="?"
elif [ "$SORRY_STATUS" -ne 0 ] || [ -z "$SORRIES" ]; then
  SORRIES=0
fi
AXIOMS=$(timeout 3 sh -c 'make axiom-count 2>/dev/null | grep "TOTAL" | awk '"'"'{print $2}'"'"'')
AXIOM_STATUS=$?
if [ "$AXIOM_STATUS" -eq 124 ]; then
  AXIOMS="?"
elif [ "$AXIOM_STATUS" -ne 0 ] || [ -z "$AXIOMS" ]; then
  AXIOMS="?"
fi
SKILL_LINES=$(wc -l < .claude/skill-document.md 2>/dev/null | tr -d ' ')

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 Sorries: $SORRIES | Axioms: $AXIOMS"
echo "📄 skill-document.md: $SKILL_LINES/100 lines"
if [ "$SKILL_LINES" -gt 100 ] 2>/dev/null; then
  echo "⚠️  Compress skill-document.md!"
fi
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
