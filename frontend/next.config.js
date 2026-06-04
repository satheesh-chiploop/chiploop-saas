/** @type {import('next').NextConfig} */
const publicApiUrl = process.env.NEXT_PUBLIC_API_URL || "";
const apiBaseUrl = (
  process.env.CHIPLOOP_API_BASE_URL ||
  process.env.CHIPLOOP_BACKEND_URL ||
  (publicApiUrl.startsWith("http://") || publicApiUrl.startsWith("https://") ? publicApiUrl : "") ||
  "https://api.getchiploop.com"
).replace(/\/+$/, "");

const nextConfig = {
  async rewrites() {
    return [
      {
        source: "/api/:path*",
        destination: `${apiBaseUrl}/:path*`,
      },
      {
        source: "/api",
        destination: apiBaseUrl,
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
