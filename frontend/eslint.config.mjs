import { defineConfig, globalIgnores } from "eslint/config";
import nextVitals from "eslint-config-next/core-web-vitals";
import nextTypeScript from "eslint-config-next/typescript";

const eslintConfig = defineConfig([
  ...nextVitals,
  ...nextTypeScript,
  globalIgnores([
      "node_modules/**",
      ".next/**",
      "out/**",
      "build/**",
      "next-env.d.ts",
  ]),
  {
    // Workflow payloads are heterogeneous JSON contracts. Keep explicit-any
    // visible during the gradual typing migration without making it the sole
    // blocker for production builds; TypeScript and Next build checks remain
    // release-blocking.
    rules: {
      "@typescript-eslint/no-explicit-any": "warn",
      "react-hooks/set-state-in-effect": "warn",
      "react-hooks/immutability": "warn",
      "react-hooks/preserve-manual-memoization": "warn",
    },
  },
]);

export default eslintConfig;
