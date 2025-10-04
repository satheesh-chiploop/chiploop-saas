"use client";
import Link from "next/link";

export default function CancelPage() {
  return (
    <div className="flex flex-col items-center justify-center h-screen bg-red-50 text-center">
      <h1 className="text-3xl font-bold text-red-600 mb-4">❌ Payment Cancelled</h1>
      <p className="text-gray-700">Your checkout session was cancelled.</p>
      <Link href="/" className="mt-6 text-blue-500 underline">
        Return to dashboard
      </Link>
    </div>
  );
}
