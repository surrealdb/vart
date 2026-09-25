#!/usr/bin/env bash
set -euo pipefail

REMOTE_HOST="tobie@192.168.1.13"
REMOTE_DIR="Repositories/vart"
WORKTREE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

echo "==> Synchronizing worktree to ${REMOTE_HOST}:${REMOTE_DIR}/..."
rsync -az --delete \
    --exclude 'target' \
    --exclude '.git' \
    "${WORKTREE_DIR}/" "${REMOTE_HOST}:${REMOTE_DIR}/"

MODE="${1:---all}"

echo "==> Running benchmarks remotely on AMD Ryzen Threadripper 9970X (32-Cores)..."

if [[ "$MODE" == "--criterion" || "$MODE" == "--all" ]]; then
    echo "--- Running Criterion comparison benchmarks ---"
    ssh "${REMOTE_HOST}" "bash -lc 'source ~/.cargo/env && cd ${REMOTE_DIR} && cargo bench --bench comparison_bench'"
fi

if [[ "$MODE" == "--divan" || "$MODE" == "--all" ]]; then
    echo "--- Running Divan memory & allocation benchmarks ---"
    ssh "${REMOTE_HOST}" "bash -lc 'source ~/.cargo/env && cd ${REMOTE_DIR} && cargo bench --bench alloc_comparison'"
fi

echo "==> Fetching benchmark reports from remote..."
mkdir -p "${WORKTREE_DIR}/target"
rsync -az "${REMOTE_HOST}:${REMOTE_DIR}/target/criterion" "${WORKTREE_DIR}/target/" 2>/dev/null || true

echo "==> Remote benchmarks completed successfully."
