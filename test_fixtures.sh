#!/bin/bash
# Test script for TAIL fixtures
# Builds TAIL and runs tailverify on all test fixtures

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "=== Building TAIL ==="
lake build
echo ""

PASS_COUNT=0
FAIL_COUNT=0

run_test() {
    local fixture_name="$1"
    local fixture_path="$2"
    local extra_args="$3"
    local expect_pass="$4"

    echo "--- Testing: $fixture_name ---"

    # Copy shared packages from main repo to avoid rebuilding mathlib
    echo "Setting up $fixture_name..."
    rm -rf "$fixture_path/.lake"
    mkdir -p "$fixture_path/.lake"
    cp -R "$SCRIPT_DIR/.lake/packages" "$fixture_path/.lake/packages"

    # Build the fixture (only needs to compile the fixture's own code)
    echo "Building $fixture_name..."
    (cd "$fixture_path" && lake update && lake build) || {
        echo "Warning: Build failed for $fixture_name, continuing anyway..."
    }
    echo ""

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
