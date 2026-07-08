"use client";
import Link from "next/link";

export default function SuccessPage() {
  return (
    <div className="flex min-h-screen flex-col items-center justify-center bg-green-50 px-4 text-center">
      <h1 className="mb-4 text-3xl font-bold text-green-600">Payment Successful</h1>
      <p className="text-gray-700">Thank you for upgrading to the Digital Loop Plan.</p>
      <Link href="/" className="mt-6 text-blue-500 underline">
        Go back to dashboard
      </Link>
    </div>
  );
}
