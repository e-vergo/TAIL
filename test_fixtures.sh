#!/bin/bash
# test_fixtures.sh - Build and verify all TAIL test fixtures
# Outputs saved to each fixture's directory as tail_report.txt

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "========================================"
echo "TAIL Test Fixtures Runner"
echo "========================================"
echo ""

# Build TAIL first
echo -e "${YELLOW}Building TAIL...${NC}"
lake build
echo -e "${GREEN}TAIL built successfully${NC}"
echo ""

PASSED=0
FAILED=0

run_test() {
    local fixture="$1"
    local expected="$2"
    local strict_flag="$3"
    local fixture_name=$(basename "$fixture")

    echo "----------------------------------------"
    echo -e "${YELLOW}Testing: $fixture_name${NC}"
    echo "----------------------------------------"

    # Build the fixture
    echo "  Building..."
    if ! (cd "$fixture" && lake build 2>&1 | tail -5); then
        echo -e "  ${RED}Build failed for $fixture_name${NC}"
        FAILED=$((FAILED + 1))
        return
    fi

    # Run verification and save output
    local output_file="$fixture/tail_report.txt"
    echo "  Verifying..."

    if lake exe tailverify $strict_flag "$fixture" > "$output_file" 2>&1; then
        actual="pass"
    else
        actual="fail"
    fi

    echo "  Output saved to: $output_file"

    # Check if result matches expectation
    if [ "$actual" == "$expected" ]; then
        echo -e "  ${GREEN}✓ Result: $actual (expected: $expected)${NC}"
        PASSED=$((PASSED + 1))
    else
        echo -e "  ${RED}✗ Result: $actual (expected: $expected)${NC}"
        FAILED=$((FAILED + 1))
    fi
    echo ""
}

# Run tests
run_test "TestFixtures/PassAll" "pass" ""
run_test "TestFixtures/PassAllStrict" "pass" "--strict"
run_test "TestFixtures/FailAll" "fail" ""
run_test "TestFixtures/FailAllStrict" "fail" "--strict"

echo "========================================"
echo "SUMMARY"
echo "========================================"
echo -e "Passed: ${GREEN}$PASSED${NC}"
echo -e "Failed: ${RED}$FAILED${NC}"
echo ""

if [ $FAILED -eq 0 ]; then
    echo -e "${GREEN}All tests passed!${NC}"
    exit 0
else
    echo -e "${RED}Some tests failed.${NC}"
    exit 1
fi
