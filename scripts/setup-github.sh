#!/usr/bin/env bash
# One-time GitHub setup for releases, through the gh CLI (needs `gh auth login` with repo admin).
#   scripts/setup-github.sh              create the environments pypi, npm and crates
#   scripts/setup-github.sh secrets      ...then prompt for the secrets (input is hidden)
# Safe to run again: environments are updated in place and a secret is only replaced if you type one.
set -euo pipefail

REPO="${GITHUB_REPOSITORY:-$(gh repo view --json nameWithOwner -q .nameWithOwner)}"
ME_ID=$(gh api user -q .id)
ME=$(gh api user -q .login)

env_create() { # name
  # Publishing waits for an approval from you, and runs only for tags v*, never for a branch.
  gh api -X PUT "repos/$REPO/environments/$1" --input - >/dev/null <<JSON
{
  "reviewers": [{ "type": "User", "id": $ME_ID }],
  "deployment_branch_policy": { "protected_branches": false, "custom_branch_policies": true }
}
JSON
  existing=$(gh api "repos/$REPO/environments/$1/deployment-branch-policies" -q '.branch_policies[].name' || true)
  if ! grep -qx 'v*' <<<"$existing"; then
    gh api -X POST "repos/$REPO/environments/$1/deployment-branch-policies" -f name='v*' -f type=tag >/dev/null
  fi
  echo "environment $1: ready (reviewer $ME, tags v* only)"
}

secret_set() { # environment, name, hint
  local value
  read -r -s -p "$2 for environment $1 ($3; empty to skip): " value; echo
  if [ -n "$value" ]; then
    gh secret set "$2" --env "$1" --repo "$REPO" --body "$value"
    echo "secret $2 set in $1"
  fi
}

echo "repository $REPO"
for e in pypi npm crates; do env_create "$e"; done

# PyPI needs no secret: it uses trusted publishing, configured on pypi.org (see PUBLISHING.md).
if [ "${1:-}" = secrets ]; then
  secret_set npm    NPM_TOKEN            "npmjs.com → Access Tokens → granular, read/write, scope @lean-elpi"
  secret_set crates CARGO_REGISTRY_TOKEN "crates.io → Account Settings → API Tokens, scopes publish-new + publish-update"
fi

echo
gh api "repos/$REPO/environments" -q '.environments[] | "  environment " + .name'
echo "secrets:"; for e in npm crates; do echo "  $e: $(gh secret list --env "$e" --repo "$REPO" | awk '{print $1}' | tr '\n' ' ')"; done
