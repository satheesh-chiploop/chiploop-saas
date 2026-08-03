export type LoopMetricKey = "agents" | "workflows" | "apps" | "productJourneys" | "referenceJourneys";

export type LoopCatalogMetric = {
  agents: number;
  workflows: number;
  apps: number;
  productJourneys: number;
  referenceJourneys: number;
};

// Authoritative UI snapshot of the current backend registry and published app/journey catalog.
// Landing and loop surfaces must import this table instead of maintaining independent counts.
export const loopCatalogMetrics: Record<string, LoopCatalogMetric> = {
  "physical-ai": { agents: 4, workflows: 1, apps: 1, productJourneys: 1, referenceJourneys: 1 },
  digital: { agents: 47, workflows: 6, apps: 9, productJourneys: 2, referenceJourneys: 5 },
  "digital-implementation": { agents: 41, workflows: 6, apps: 8, productJourneys: 2, referenceJourneys: 3 },
  fpga: { agents: 22, workflows: 4, apps: 10, productJourneys: 1, referenceJourneys: 2 },
  analog: { agents: 22, workflows: 4, apps: 8, productJourneys: 1, referenceJourneys: 1 },
  "mixed-signal": { agents: 77, workflows: 6, apps: 13, productJourneys: 2, referenceJourneys: 2 },
  firmware: { agents: 62, workflows: 4, apps: 11, productJourneys: 3, referenceJourneys: 5 },
  validation: { agents: 17, workflows: 2, apps: 5, productJourneys: 3, referenceJourneys: 4 },
};
