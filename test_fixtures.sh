#!/bin/bash
# Test script for TAIL fixtures
# Builds TAIL and runs tailverify on all test fixtures

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "=== Building TAIL ==="
lake build
echo ""

# Check if SafeVerify is available
SAFEVERIFY_AVAILABLE=false
if lake exe safe_verify --help >/dev/null 2>&1; then
    SAFEVERIFY_AVAILABLE=true
    echo "SafeVerify detected - will run SafeVerify tests"
else
    echo "SafeVerify not installed - skipping SafeVerify tests"
fi
echo ""

PASS_COUNT=0
FAIL_COUNT=0

# Setup a fixture by fetching cache and building
setup_fixture() {
    local fixture_path="$1"
    local fixture_name="$2"

    echo "Setting up $fixture_name..."

    # Remove any broken symlinks
    if [ -L "$fixture_path/.lake/packages" ]; then
        rm "$fixture_path/.lake/packages"
    fi

    # Fetch cache and build
    echo "Fetching cache and building $fixture_name..."
    (cd "$fixture_path" && lake exe cache get && lake build) || {
        echo "Warning: Setup failed for $fixture_name, continuing anyway..."
    }
}

run_test() {
    local fixture_name="$1"
    local fixture_path="$2"
    local extra_args="$3"
    local expect_pass="$4"

    echo "--- Testing: $fixture_name ---"

    # Run tailverify and capture exit code
    set +e
    output=$(lake exe tailverify "$fixture_path" $extra_args 2>&1)
    exit_code=$?
    set -e

    echo "$output"
    echo ""

    if [ "$expect_pass" = "true" ]; then
        if [ $exit_code -eq 0 ]; then
            echo "PASS: $fixture_name (expected pass, got pass)"
            ((PASS_COUNT++))
        else
            echo "FAIL: $fixture_name (expected pass, got fail)"
            ((FAIL_COUNT++))
        fi
    else
        if [ $exit_code -ne 0 ]; then
            echo "PASS: $fixture_name (expected fail, got fail)"
            ((PASS_COUNT++))
        else
            echo "FAIL: $fixture_name (expected fail, got pass)"
            ((FAIL_COUNT++))
        fi
    fi
    echo ""
}

echo "=== Setting Up Test Fixtures ==="
echo ""

# Setup all fixtures first (they share the same mathlib version, so cache is reused)
setup_fixture "TestFixtures/PassAll" "PassAll"
setup_fixture "TestFixtures/PassAllStrict" "PassAllStrict"
setup_fixture "TestFixtures/FailAll" "FailAll"
setup_fixture "TestFixtures/FailAllStrict" "FailAllStrict"

echo ""
echo "=== Running Tests ==="
echo ""

# PassAll - default mode, should pass
run_test "PassAll" "TestFixtures/PassAll" "" "true"

# PassAllStrict - strict mode, should pass
run_test "PassAllStrict" "TestFixtures/PassAllStrict" "--strict" "true"

# FailAll - default mode, should fail
run_test "FailAll" "TestFixtures/FailAll" "" "false"

# FailAllStrict - strict mode, should fail
run_test "FailAllStrict" "TestFixtures/FailAllStrict" "--strict" "false"

# SafeVerify tests (only if SafeVerify is installed)
if [ "$SAFEVERIFY_AVAILABLE" = "true" ]; then
    echo ""
    echo "=== SafeVerify Tests ==="
    echo ""

    # PassAll with SafeVerify - should pass
    run_test "PassAll+SafeVerify" "TestFixtures/PassAll" "--safeverify" "true"

    # FailAll with SafeVerify - should fail
    run_test "FailAll+SafeVerify" "TestFixtures/FailAll" "--safeverify" "false"
fi

echo "=== Summary ==="
echo "Passed: $PASS_COUNT"
echo "Failed: $FAIL_COUNT"
echo ""

if [ $FAIL_COUNT -gt 0 ]; then
    echo "SOME TESTS FAILED"
    exit 1
else
    echo "ALL TESTS PASSED"
    exit 0
fi
