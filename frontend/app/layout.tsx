import type { Metadata } from "next";
import { Geist, Geist_Mono } from "next/font/google";
import "./globals.css";

const geistSans = Geist({
  variable: "--font-geist-sans",
  subsets: ["latin"],
});

const geistMono = Geist_Mono({
  variable: "--font-geist-mono",
  subsets: ["latin"],
});

export const metadata: Metadata = {
  metadataBase: new URL("https://www.getchiploops.com"),
  title: {
    default: "ChipLoop | Agentic AI for Chip Design",
    template: "%s | ChipLoop",
  },
  description:
    "Build chip design workflows with AI agents for architecture, RTL, simulation, firmware, and analysis.",
  applicationName: "ChipLoop",
  alternates: {
    canonical: "/",
  },
  openGraph: {
    type: "website",
    url: "https://www.getchiploops.com",
    siteName: "ChipLoop",
    title: "ChipLoop | Agentic AI for Chip Design",
    description:
      "Build chip design workflows with AI agents for architecture, RTL, simulation, firmware, and analysis.",
    images: [
      {
        url: "/og-chiploop.png",
        width: 1200,
        height: 630,
        alt: "ChipLoop agentic AI chip design workflows",
      },
    ],
  },
  twitter: {
    card: "summary_large_image",
    title: "ChipLoop | Agentic AI for Chip Design",
    description:
      "Build chip design workflows with AI agents for architecture, RTL, simulation, firmware, and analysis.",
    images: ["/og-chiploop.png"],
  },
  icons: {
    icon: "/favicon.ico",
    apple: "/apple-touch-icon.png",
  },
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="en">
      <body
        className={`${geistSans.variable} ${geistMono.variable} antialiased`}
      >
        {children}
      </body>
    </html>
  );
}
