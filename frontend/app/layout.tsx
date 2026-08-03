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
    default: "ChipLoop | Agentic AI for Physical AI and Silicon Development",
    template: "%s | ChipLoop",
  },
  description:
    "All-in-one Agentic AI platform for Physical AI and Silicon Development, from physics models to RTL, FPGA, firmware, validation, and product delivery.",
  applicationName: "ChipLoop",
  alternates: {
    canonical: "/",
  },
  openGraph: {
    type: "website",
    url: "https://www.getchiploops.com",
    siteName: "ChipLoop",
    title: "ChipLoop | Agentic AI for Physical AI and Silicon Development",
    description:
      "All-in-one Agentic AI platform for Physical AI and Silicon Development, from physics models to RTL, FPGA, firmware, validation, and product delivery.",
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
    title: "ChipLoop | Agentic AI for Physical AI and Silicon Development",
    description:
      "All-in-one Agentic AI platform for Physical AI and Silicon Development, from physics models to RTL, FPGA, firmware, validation, and product delivery.",
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
