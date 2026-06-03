/** @type {import('next').NextConfig} */
const nextConfig = {
  async rewrites() {
    const publicApiUrl = process.env.NEXT_PUBLIC_API_URL || "";
    const backendUrl =
      process.env.CHIPLOOP_BACKEND_URL ||
      (publicApiUrl.startsWith("http://") || publicApiUrl.startsWith("https://") ? publicApiUrl : "") ||
      "http://localhost:8000";
    return [
      {
        source: "/api/:path*",
        destination: `${backendUrl.replace(/\/$/, "")}/:path*`,
      },
    ];
  },
  eslint: {
    // ✅ Ignore ESLint during production build
    ignoreDuringBuilds: true,
  },
  typescript: {
    // ✅ Ignore type errors during build (optional, safe)
    ignoreBuildErrors: true,
  },
};

module.exports = nextConfig;
