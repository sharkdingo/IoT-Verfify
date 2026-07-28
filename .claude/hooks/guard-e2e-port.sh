#!/usr/bin/env bash
# Blocks a Playwright run while something already holds port 3000.
#
# Why this is a hook and not a written rule: Playwright's web server would otherwise be adopted
# from whatever is already on the port. With `reuseExistingServer: false` that now fails loudly,
# but the failure appears mid-suite and is easy to misread as a product problem. Catching it
# before the command runs turns a confusing red run into one actionable sentence.
#
# Exit 0 = allow. Exit 2 = block and show stderr to the agent.
set -uo pipefail

payload=$(cat)

# Only inspect commands that actually start Playwright.
case "$payload" in
  *playwright*|*test:e2e*) ;;
  *) exit 0 ;;
esac

# An explicitly managed server is the documented escape hatch.
if [ -n "${E2E_BASE_URL:-}" ]; then
  exit 0
fi

listener=$(netstat -ano 2>/dev/null | grep -E 'LISTENING' | grep -E '[:.]3000[[:space:]]' | head -1 || true)
if [ -n "$listener" ]; then
  cat >&2 <<'MSG'
Port 3000 is already in use, so the E2E run would fail once Playwright tries to start its
web server (reuseExistingServer is off deliberately, so a leftover dev server cannot be
adopted and silently tested instead of a fresh production build).

Free port 3000 first, or set E2E_BASE_URL to a server you are managing yourself.
MSG
  exit 2
fi

exit 0
