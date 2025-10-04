export default function SuccessPage() {
  return (
    <div className="flex flex-col items-center justify-center h-screen bg-green-50 text-center">
      <h1 className="text-3xl font-bold text-green-600 mb-4">✅ Payment Successful!</h1>
      <p className="text-gray-700">Thank you for upgrading to the Digital Loop Plan.</p>
      <a href="/" className="mt-6 text-blue-500 underline">Go back to dashboard</a>
    </div>
  );
}
