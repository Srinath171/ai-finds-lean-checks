"""Run all offline tests from an importable Windows-spawn-safe module."""
import sys
import unittest


def main():
    loader = unittest.defaultTestLoader
    suite = loader.discover('tests')
    suite.addTests(loader.loadTestsFromNames([
        'hour2.test_phase_guard',
        'hour2.test_claude_guard',
        'hour2.test_joint_nand',
        'hour2.test_sat_boolean_mux',
        'continuation.test_meta_guard',
        'continuation.test_profile_sat',
        'continuation.test_low_cost_two',
        'continuation.test_low_cost_profiles',
        'continuation.test_c2_truncated_profile',
    ]))
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(main())
