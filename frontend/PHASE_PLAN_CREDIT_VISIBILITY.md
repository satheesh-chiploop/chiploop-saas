# Plan And Credit Visibility

## Goal

Make users aware of their plan and credits without turning billing into an interruption.

## UX Added

- Compact plan/credit badge in the Apps header.
- Compact plan/credit badge in the Studio header.
- Clickable badge dropdown with:
  - current plan
  - credits remaining
  - monthly credits
  - trial days remaining when applicable
  - link to Settings > Plan
- Low-credit FYI banner when credits remaining are below 20%.

## Non-Annoying Rules

- The low-credit banner is informational only.
- No automatic modal is shown for normal usage.
- Users can dismiss the low-credit banner for 24 hours.
- The banner is not shown during first-run onboarding.
- Upgrade/plan details are available through Settings > Plan.

## Backend Endpoint Used

- `GET /api/settings/plan`

The browser continues to use Supabase session auth through the shared API client.

## Future Blocked Action Behavior

If backend later returns a hard block such as insufficient credits or feature not enabled, the UI can show a modal at that moment only. The current implementation intentionally avoids proactive popups.

## Validation

- `/apps` shows the badge for authenticated users.
- `/workflow` shows the badge for authenticated users.
- Low-credit banner appears only below 20% remaining credits.
- Dismiss hides the banner for 24 hours.
- Settings > Plan remains the source of full detail.
