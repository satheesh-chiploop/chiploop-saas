# Webinar Registration

Adds a public registration path for the weekly ChipLoop webinar.

## Frontend

- Landing page CTA: `/`
- Registration page: `/webinar/register`
- Browser posts to `/api/webinar/register`

Fields collected:

- name
- email
- company/school
- role
- loop interest
- preferred session
- questions/topics

## Backend

Public endpoint:

```text
POST /webinar/register
```

The endpoint validates basic required fields and stores registrations in `webinar_registrations` when the Supabase migration is applied.

## Supabase

Run manually:

```text
supabase/migrations/phase_webinar_registrations.sql
```

No secrets are stored in code. No frontend auth is required for public webinar registration.
