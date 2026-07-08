"use client";
import Link from "next/link";

export default function CancelPage() {
  return (
    <div className="flex min-h-screen flex-col items-center justify-center bg-red-50 px-4 text-center">
      <h1 className="mb-4 text-3xl font-bold text-red-600">Payment Cancelled</h1>
      <p className="text-gray-700">Your checkout session was cancelled.</p>
      <Link href="/" className="mt-6 text-blue-500 underline">
        Return to dashboard
      </Link>
    </div>
  );
}
