"""Offline subscription-routing regressions; no auth command or model is run."""
import unittest
from unittest.mock import patch
from continuation.team.controller import claude_subscription_preflight, TeamError


class SubscriptionTests(unittest.TestCase):
    def test_safe_oauth_auth_proof_discards_identity_and_api_environment(self):
        calls = []
        def capture(args, prompt, timeout, **kwargs):
            calls.append((args, prompt, timeout, kwargs))
            return {'loggedIn': True, 'authMethod': 'claude.ai', 'apiProvider': 'firstParty',
                    'subscriptionType': 'team', 'email': 'private@example.invalid', 'apiKey': 'never-copy'}
        with patch.dict('os.environ', {'ANTHROPIC_API_KEY': 'secret', 'CLAUDE_CODE_USE_BEDROCK': '1'}):
            result = claude_subscription_preflight(object(), capture=capture, claude='fixed-claude')
        self.assertEqual(result, {'logged_in': True, 'auth_method': 'claude.ai',
                                 'api_provider': 'firstParty', 'subscription_type': 'team'})
        self.assertEqual(calls[0][:3], (['fixed-claude', 'auth', 'status'], '', 20))
        self.assertNotIn('ANTHROPIC_API_KEY', calls[0][3]['env'])
        self.assertNotIn('CLAUDE_CODE_USE_BEDROCK', calls[0][3]['env'])
        self.assertEqual(calls[0][3]['capture_limit'], 65536)

    def test_api_or_unverified_auth_is_rejected(self):
        valid = {'loggedIn': True, 'authMethod': 'claude.ai', 'apiProvider': 'firstParty', 'subscriptionType': 'team'}
        for patch_values in ({'loggedIn': False}, {'loggedIn': 1}, {'authMethod': 'api_key'},
                             {'apiProvider': 'bedrock'}, {'subscriptionType': None}, {'subscriptionType': 'api'}):
            with self.subTest(patch_values=patch_values):
                with self.assertRaises(TeamError):
                    claude_subscription_preflight(object(), capture=lambda *a, **kw: valid | patch_values, claude='fixed')


if __name__ == '__main__': unittest.main()
