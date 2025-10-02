'use client'
import { supabase } from '@/lib/supabaseClient'
import { useRouter } from 'next/navigation'
import { useState } from 'react'

export default function LoginPage() {
  const [email, setEmail] = useState('')
  const [password, setPassword] = useState('')
  const router = useRouter()

  // ---- Email + Password ----
  const signInWithEmail = async () => {
    if (!email || !password) {
      alert('Please enter both email and password')
      return
    }
    const { error } = await supabase.auth.signInWithPassword({ email, password })
    if (error) alert(error.message)
    else router.push('/workflow')
  }

  const signUpWithEmail = async () => {
    if (!email || !password) {
      alert('Please enter both email and password')
      return
    }
    const { error } = await supabase.auth.signUp({ email, password })
    if (error) alert(error.message)
    else alert('Check your email to confirm signup!')
  }

  // ---- Magic Link ----
  const sendMagicLink = async () => {
    if (!email) {
      alert('Enter your email first')
      return
    }
    const { error } = await supabase.auth.signInWithOtp({ email })
    if (error) alert(error.message)
    else alert('Check your email for a login link')
  }

  // ---- OAuth Providers ----
  const signInOAuth = async (provider: 'github' | 'google') => {
    const { error } = await supabase.auth.signInWithOAuth({ provider })
    if (error) alert(error.message)
  }

  return (
    <div className="h-screen flex items-center justify-center bg-slate-900 text-white">
      <div className="p-8 bg-slate-800 rounded-lg shadow-lg w-96">
        <h1 className="text-2xl font-bold mb-4 text-center">Login to ChipLoop</h1>

        {/* Email + Password */}
        <input
          type="email"
          placeholder="Email"
          value={email}
          onChange={(e) => setEmail(e.target.value)}
          className="w-full mb-3 p-2 rounded bg-slate-700"
        />
        <input
          type="password"
          placeholder="Password"
          value={password}
          onChange={(e) => setPassword(e.target.value)}
          className="w-full mb-3 p-2 rounded bg-slate-700"
        />

        <div className="flex gap-2 mb-3">
          <button
            onClick={signInWithEmail}
            className="flex-1 bg-cyan-500 hover:bg-cyan-400 text-black font-bold py-2 px-4 rounded"
          >
            Login
          </button>
          <button
            onClick={signUpWithEmail}
            className="flex-1 bg-green-500 hover:bg-green-400 text-black font-bold py-2 px-4 rounded"
          >
            Sign Up
          </button>
        </div>

        {/* Magic Link */}
        <button
          onClick={sendMagicLink}
          className="w-full bg-yellow-500 hover:bg-yellow-400 text-black font-bold py-2 px-4 rounded mb-3"
        >
          Send Magic Link
        </button>

        {/* OAuth Providers */}
        <button
          onClick={() => signInOAuth('github')}
          className="w-full bg-black hover:bg-gray-800 text-white font-bold py-2 px-4 rounded mb-2"
        >
          Continue with GitHub
        </button>
        <button
          onClick={() => signInOAuth('google')}
          className="w-full bg-red-500 hover:bg-red-400 text-white font-bold py-2 px-4 rounded"
        >
          Continue with Google
        </button>
      </div>
    </div>
  )
}
