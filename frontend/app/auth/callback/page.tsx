'use client'
import { useRouter } from 'next/navigation'
import { useEffect } from 'react'

export default function CallbackPage() {
  const router = useRouter()

  useEffect(() => {
    // Supabase handles session automatically.
    // Just send user back home after login.
    setTimeout(() => router.replace('/'), 500)
  }, [router])

  return <p>Completing sign-in…</p>
}
