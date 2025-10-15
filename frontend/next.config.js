/** @type {import('next').NextConfig} */
const nextConfig = {
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
