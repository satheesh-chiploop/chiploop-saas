import type { NextConfig } from "next";

const apiBaseUrl = (process.env.CHIPLOOP_API_BASE_URL || "https://api.getchiploop.com").replace(/\/+$/, "");

const nextConfig: NextConfig = {
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
};

export default nextConfig;
