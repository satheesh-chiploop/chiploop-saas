"use client";

import { useEffect, useMemo, useState } from "react";
import { useRouter } from "next/navigation";
import TopNav from "@/components/TopNav";
import { LowCreditBanner } from "@/components/PlanCreditStatus";
import { apiDelete, apiGet, apiPatch, apiPost } from "@/lib/apiClient";
import { createClientComponentClient } from "@/lib/platformClient";

type ProductType = "digital" | "analog" | "mixed_signal" | "embedded" | "validation";

type ReferenceJourney = {
  id?: string | null;
  slug: string;
  name: string;
  product_type: ProductType | string;
  summary: string;
  stage_count: number;
  definition: {
    stages?: Array<{
      id: string;
      label: string;
      app: string;
      required?: boolean;
      recommended?: boolean;
      optional?: boolean;
    }>;
  };
};

type Product = {
  id: string;
  name: string;
  product_type: ProductType | string;
  starting_point: string;
  description: string;
  status: string;
  stage_config?: {
    stages?: Array<{ id: string; label: string; app: string; required?: boolean; recommended?: boolean; optional?: boolean }>;
  };
  updated_at?: string;
};

const supabase = createClientComponentClient();

const PRODUCT_TYPES: Array<{ id: ProductType; label: string; description: string }> = [
  { id: "digital", label: "Digital", description: "Arch2RTL, RTL quality, verification, synthesis, closure, and implementation handoff." },
  { id: "analog", label: "Analog", description: "Specs, behavioral models, SPICE/GDS collateral, LEF/LIB consistency." },
  { id: "mixed_signal", label: "Mixed-Signal", description: "System RTL, analog/digital interfaces, System Sim, System Synthesis, and optional PD/product handoff." },
  { id: "embedded", label: "Embedded", description: "Register extraction, HAL, drivers, firmware, software services, co-simulation, and app handoff." },
  { id: "validation", label: "Validation", description: "Validation plans, bench/instrument setup, connectivity, preflight, execution orchestration, analytics, and reports." },
];

const STARTING_POINTS = [
  { id: "from_specs", label: "From specs" },
  { id: "from_existing_rtl", label: "From existing RTL" },
  { id: "from_existing_workflow", label: "From existing workflow" },
  { id: "from_uploaded_collateral", label: "From uploaded collateral" },
];

function typeLabel(value: string) {
  return value.replace(/_/g, "-").replace(/\b\w/g, (letter) => letter.toUpperCase());
}

function stageBadge(stage: { required?: boolean; recommended?: boolean; optional?: boolean }) {
  if (stage.required) return "Required";
  if (stage.recommended) return "Recommended";
  if (stage.optional) return "Optional";
  return "Stage";
}

function StepRail({ active }: { active: "define" | "configure" | "run" }) {
  const steps = [
    { id: "define", label: "Define", text: "Create product" },
    { id: "configure", label: "Configure", text: "Review stages" },
    { id: "run", label: "Run", text: "Track results" },
  ] as const;
  return (
    <div className="grid gap-2 rounded-lg border border-slate-800 bg-slate-900/45 p-3 sm:grid-cols-3">
      {steps.map((step, index) => (
        <div
          key={step.id}
          className={`rounded-md border px-3 py-2 ${
            active === step.id ? "border-cyan-400 bg-cyan-500/10" : "border-slate-800 bg-slate-950/60"
          }`}
        >
          <div className="text-xs font-semibold uppercase text-slate-500">Step {index + 1}</div>
          <div className={active === step.id ? "text-sm font-semibold text-slate-100" : "text-sm font-semibold text-white"}>{step.label}</div>
          <div className="mt-1 text-xs text-slate-400">{step.text}</div>
        </div>
      ))}
    </div>
  );
}

export default function ProductsPage() {
  const router = useRouter();
  const [authChecked, setAuthChecked] = useState(false);
  const [isLoggedIn, setIsLoggedIn] = useState(false);
  const [references, setReferences] = useState<ReferenceJourney[]>([]);
  const [products, setProducts] = useState<Product[]>([]);
  const [selectedReference, setSelectedReference] = useState<string>("");
  const [productType, setProductType] = useState<ProductType>("digital");
  const [startingPoint, setStartingPoint] = useState("from_specs");
  const [productName, setProductName] = useState("");
  const [description, setDescription] = useState("");
  const [busy, setBusy] = useState(false);
  const [editingProductId, setEditingProductId] = useState<string | null>(null);
  const [editDraft, setEditDraft] = useState<Partial<Product>>({});
  const [deletingProductId, setDeletingProductId] = useState<string | null>(null);
  const [deleteConfirmName, setDeleteConfirmName] = useState("");
  const [message, setMessage] = useState<string | null>(null);

  const selectedReferenceData = useMemo(
    () => references.find((reference) => reference.slug === selectedReference) || null,
    [references, selectedReference],
  );

  useEffect(() => {
    let mounted = true;
    (async () => {
      const { data: { session } } = await supabase.auth.getSession();
      if (!mounted) return;
      setIsLoggedIn(Boolean(session?.user));
      setAuthChecked(true);
    })();
    return () => { mounted = false; };
  }, []);

  useEffect(() => {
    let mounted = true;
    (async () => {
      try {
        const refs = await apiGet<{ status: string; reference_journeys: ReferenceJourney[] }>("/products/reference-journeys");
        if (mounted) setReferences(refs.reference_journeys || []);
      } catch (error) {
        if (mounted) setMessage(error instanceof Error ? error.message : "Failed to load starter products");
      }
    })();
    return () => { mounted = false; };
  }, []);

  useEffect(() => {
    if (!authChecked || !isLoggedIn) return;
    let mounted = true;
    (async () => {
      try {
        const out = await apiGet<{ status: string; products: Product[] }>("/products");
        if (mounted) setProducts(out.products || []);
      } catch (error) {
        if (mounted) setMessage(error instanceof Error ? error.message : "Failed to load products");
      }
    })();
    return () => { mounted = false; };
  }, [authChecked, isLoggedIn]);

  useEffect(() => {
    if (!selectedReferenceData) return;
    setProductType((selectedReferenceData.product_type as ProductType) || "digital");
    if (!productName.trim()) setProductName(selectedReferenceData.name);
    if (!description.trim()) setDescription(selectedReferenceData.summary);
  }, [selectedReferenceData, productName, description]);

  async function createProduct() {
    if (!isLoggedIn) {
      router.push("/login?next=/products");
      return;
    }
    if (!productName.trim()) {
      setMessage("Product name is required.");
      return;
    }
    setBusy(true);
    setMessage(null);
    try {
      const out = await apiPost<{ status: string; product: Product }>("/products", {
        name: productName.trim(),
        product_type: productType,
        starting_point: startingPoint,
        description: description.trim(),
        reference_slug: selectedReference || undefined,
      });
      setProducts((current) => [out.product, ...current.filter((item) => item.id !== out.product.id)]);
      setMessage("Product created. Opening stage review.");
      router.push(`/products/${out.product.id}`);
    } catch (error) {
      setMessage(error instanceof Error ? error.message : "Failed to create product");
    } finally {
      setBusy(false);
    }
  }

  function beginEditProduct(product: Product) {
    setEditingProductId(product.id);
    setEditDraft({
      name: product.name,
      product_type: product.product_type,
      starting_point: product.starting_point,
      description: product.description,
      status: product.status,
    });
    setDeletingProductId(null);
    setDeleteConfirmName("");
    setMessage(null);
  }

  async function saveProductEdit(productId: string) {
    const name = String(editDraft.name || "").trim();
    if (!name) {
      setMessage("Product name is required.");
      return;
    }
    setBusy(true);
    setMessage(null);
    try {
      const out = await apiPatch<{ status: string; product: Product }>(`/products/${productId}`, {
        name,
        product_type: editDraft.product_type,
        starting_point: editDraft.starting_point,
        description: String(editDraft.description || "").trim(),
        status: editDraft.status,
      });
      setProducts((current) => current.map((item) => (item.id === productId ? out.product : item)));
      setEditingProductId(null);
      setEditDraft({});
      setMessage("Product updated.");
    } catch (error) {
      setMessage(error instanceof Error ? error.message : "Failed to update product");
    } finally {
      setBusy(false);
    }
  }

  async function deleteProduct(product: Product) {
    if (deleteConfirmName !== product.name) {
      setMessage(`Type "${product.name}" to confirm delete.`);
      return;
    }
    setBusy(true);
    setMessage(null);
    try {
      await apiDelete<{ status: string; deleted_product_id: string }>(`/products/${product.id}`);
      setProducts((current) => current.filter((item) => item.id !== product.id));
      setDeletingProductId(null);
      setDeleteConfirmName("");
      if (editingProductId === product.id) {
        setEditingProductId(null);
        setEditDraft({});
      }
      setMessage("Product deleted.");
    } catch (error) {
      setMessage(error instanceof Error ? error.message : "Failed to delete product");
    } finally {
      setBusy(false);
    }
  }

  return (
    <main className="min-h-screen bg-slate-950 text-slate-100">
      <TopNav current="products" showPlanBadge />
      <div className="mx-auto max-w-[1680px] px-4 py-6 sm:px-6">
        <LowCreditBanner />

        <section className="mb-6">
          <div className="text-xs font-semibold uppercase text-cyan-300">Products</div>
          <h1 className="mt-2 text-4xl font-extrabold leading-tight text-white sm:text-5xl">Define, configure, and run product development</h1>
          <p className="mt-3 max-w-3xl text-sm leading-6 text-slate-300">
            Start with the product intent, review the development stages, then run the workflows with product-level lineage and results.
          </p>
        </section>

        <div className="mb-6">
          <StepRail active="define" />
        </div>

        {message ? (
          <div className="mb-5 rounded-lg border border-slate-700 bg-slate-900/70 px-4 py-3 text-sm text-slate-200">
            {message}
          </div>
        ) : null}

        <section className="mb-6 rounded-lg border border-slate-800 bg-slate-900/55 p-5">
          <div className="flex flex-col gap-4 sm:flex-row sm:items-center sm:justify-between">
            <div>
              <div className="text-xs font-semibold uppercase text-cyan-300">Project Review</div>
              <h2 className="mt-1 text-lg font-semibold text-white">Already have files, reports, or a Git repo?</h2>
              <p className="mt-2 max-w-3xl text-sm leading-6 text-slate-300">
                Use Ask this Project with Smart Context to summarize the codebase, identify risks, and get recommended product stages before configuring the product journey.
              </p>
            </div>
            <button
              type="button"
              onClick={() => router.push("/apps/ask-project")}
              className="shrink-0 rounded-lg bg-cyan-400 px-4 py-2 text-sm font-semibold text-slate-950 hover:bg-cyan-300"
            >
              Ask this Project
            </button>
          </div>
        </section>

        <div className="grid gap-5 lg:grid-cols-[1.05fr_0.95fr]">
          <section className="rounded-lg border border-slate-800 bg-slate-900/45 p-5">
            <div className="flex flex-col gap-2 sm:flex-row sm:items-start sm:justify-between">
              <div>
                <h2 className="text-xl font-semibold text-white">Step 1: Define Product</h2>
                <p className="mt-1 text-sm text-slate-400">Choose product type, starting point, and an optional reference product.</p>
              </div>
              <span className="rounded-md bg-cyan-500/10 px-2 py-1 text-xs font-semibold text-cyan-200">Define</span>
            </div>

            <div className="mt-5 grid gap-4">
              <label className="grid gap-2">
                <span className="text-sm font-medium text-slate-200">Product name</span>
                <input
                  value={productName}
                  onChange={(event) => setProductName(event.target.value)}
                  placeholder="PWM Fan Controller"
                  className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                />
              </label>

              <div>
                <div className="mb-2 text-sm font-medium text-slate-200">Product type</div>
                <div className="grid gap-2 sm:grid-cols-2">
                  {PRODUCT_TYPES.map((type) => (
                    <button
                      key={type.id}
                      type="button"
                      onClick={() => setProductType(type.id)}
                      className={`rounded-lg border p-3 text-left transition ${
                        productType === type.id
                          ? "border-cyan-400 bg-cyan-500/10"
                          : "border-slate-800 bg-slate-950/60 hover:border-slate-600"
                      }`}
                    >
                      <div className="text-sm font-semibold text-white">{type.label}</div>
                      <div className="mt-1 text-xs leading-5 text-slate-400">{type.description}</div>
                    </button>
                  ))}
                </div>
              </div>

              <label className="grid gap-2">
                <span className="text-sm font-medium text-slate-200">Starting point</span>
                <select
                  value={startingPoint}
                  onChange={(event) => setStartingPoint(event.target.value)}
                  className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                >
                  {STARTING_POINTS.map((point) => (
                    <option key={point.id} value={point.id}>{point.label}</option>
                  ))}
                </select>
              </label>

              <label className="grid gap-2">
                <span className="text-sm font-medium text-slate-200">Start from reference product</span>
                <select
                  value={selectedReference}
                  onChange={(event) => setSelectedReference(event.target.value)}
                  className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                >
                  <option value="">None, create custom product</option>
                  {references.map((reference) => (
                    <option key={reference.slug} value={reference.slug}>{reference.name}</option>
                  ))}
                </select>
                <span className="text-xs leading-5 text-slate-500">
                  Starter products prefill stage plans. Existing standalone Apps remain available while migration continues.
                </span>
              </label>

              <label className="grid gap-2">
                <span className="text-sm font-medium text-slate-200">Description</span>
                <textarea
                  value={description}
                  onChange={(event) => setDescription(event.target.value)}
                  rows={4}
                  placeholder="What is this product meant to do?"
                  className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                />
              </label>

              <button
                onClick={createProduct}
                disabled={busy}
                className="rounded-lg bg-cyan-400 px-4 py-2 text-sm font-semibold text-slate-950 transition hover:bg-cyan-300 disabled:cursor-not-allowed disabled:opacity-60"
              >
                {busy ? "Creating..." : "Create Product and Configure"}
              </button>
            </div>
          </section>

          <section className="rounded-lg border border-slate-800 bg-slate-900/45 p-5">
              <h2 className="text-xl font-semibold text-white">Existing Products</h2>
              <p className="mt-1 text-sm text-slate-400">Private to the signed-in user. Continue configuring or running product stages.</p>
            <div className="mt-5 grid gap-3">
              {!authChecked ? (
                <div className="text-sm text-slate-400">Checking session...</div>
              ) : !isLoggedIn ? (
                <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm text-slate-300">
                  Login to create and view your products.
                </div>
              ) : products.length === 0 ? (
                <div className="rounded-lg border border-slate-800 bg-slate-950/60 p-4 text-sm text-slate-300">
                  No products yet. Create one from a product type or starter product.
                </div>
              ) : (
                products.map((product) => (
                  <div key={product.id} className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
                    {editingProductId === product.id ? (
                      <div className="grid gap-3">
                        <label className="grid gap-2">
                          <span className="text-xs font-semibold uppercase text-slate-400">Name</span>
                          <input
                            value={String(editDraft.name || "")}
                            onChange={(event) => setEditDraft((current) => ({ ...current, name: event.target.value }))}
                            className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                          />
                        </label>
                        <div className="grid gap-3 sm:grid-cols-2">
                          <label className="grid gap-2">
                            <span className="text-xs font-semibold uppercase text-slate-400">Product type</span>
                            <select
                              value={String(editDraft.product_type || product.product_type)}
                              onChange={(event) => setEditDraft((current) => ({ ...current, product_type: event.target.value }))}
                              className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                            >
                              {PRODUCT_TYPES.map((type) => (
                                <option key={type.id} value={type.id}>{type.label}</option>
                              ))}
                            </select>
                          </label>
                          <label className="grid gap-2">
                            <span className="text-xs font-semibold uppercase text-slate-400">Status</span>
                            <select
                              value={String(editDraft.status || product.status)}
                              onChange={(event) => setEditDraft((current) => ({ ...current, status: event.target.value }))}
                              className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                            >
                              {["draft", "ready", "running", "completed", "failed", "archived"].map((status) => (
                                <option key={status} value={status}>{status}</option>
                              ))}
                            </select>
                          </label>
                        </div>
                        <label className="grid gap-2">
                          <span className="text-xs font-semibold uppercase text-slate-400">Description</span>
                          <textarea
                            value={String(editDraft.description || "")}
                            onChange={(event) => setEditDraft((current) => ({ ...current, description: event.target.value }))}
                            rows={3}
                            className="rounded-lg border border-slate-700 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-cyan-400"
                          />
                        </label>
                      </div>
                    ) : (
                      <>
                        <div className="flex items-start justify-between gap-3">
                          <div>
                            <button
                              onClick={() => router.push(`/products/${product.id}`)}
                              className="font-semibold text-white hover:text-cyan-200"
                            >
                              {product.name}
                            </button>
                            <div className="mt-1 text-xs text-slate-400">
                              {typeLabel(product.product_type)} / {product.starting_point.replace(/_/g, " ")}
                            </div>
                          </div>
                          <span className="rounded-md border border-slate-700 px-2 py-1 text-xs text-slate-300">{product.status}</span>
                        </div>
                        {product.description ? <p className="mt-3 text-sm leading-6 text-slate-300">{product.description}</p> : null}
                      </>
                    )}
                    {product.stage_config?.stages?.length ? (
                      <div className="mt-3 flex flex-wrap gap-2">
                        {product.stage_config.stages.slice(0, 6).map((stage) => (
                          <span key={stage.id} className="rounded-md bg-slate-800 px-2 py-1 text-xs text-slate-300">{stage.label}</span>
                        ))}
                        {product.stage_config.stages.length > 6 ? (
                          <span className="rounded-md bg-slate-800 px-2 py-1 text-xs text-slate-300">+{product.stage_config.stages.length - 6}</span>
                        ) : null}
                      </div>
                    ) : null}
                    <div className="mt-3 flex flex-wrap gap-2">
                      <button
                        onClick={() => router.push(`/products/${product.id}`)}
                        className="rounded-lg border border-slate-700 px-3 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-800"
                      >
                        Configure
                      </button>
                      {editingProductId === product.id ? (
                        <>
                          <button
                            onClick={() => saveProductEdit(product.id)}
                            disabled={busy}
                            className="rounded-lg bg-cyan-400 px-3 py-2 text-sm font-semibold text-slate-950 hover:bg-cyan-300 disabled:cursor-not-allowed disabled:opacity-60"
                          >
                            Save
                          </button>
                          <button
                            onClick={() => {
                              setEditingProductId(null);
                              setEditDraft({});
                            }}
                            className="rounded-lg border border-slate-700 px-3 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-800"
                          >
                            Cancel
                          </button>
                        </>
                      ) : (
                        <button
                          onClick={() => beginEditProduct(product)}
                          className="rounded-lg border border-slate-700 px-3 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-800"
                        >
                          Edit
                        </button>
                      )}
                      <button
                        onClick={() => {
                          setDeletingProductId(deletingProductId === product.id ? null : product.id);
                          setDeleteConfirmName("");
                        }}
                        className="rounded-lg border border-red-500/50 px-3 py-2 text-sm font-semibold text-red-200 hover:bg-red-950/40"
                      >
                        Delete
                      </button>
                    </div>
                    {deletingProductId === product.id ? (
                      <div className="mt-3 rounded-lg border border-red-500/30 bg-red-950/20 p-3">
                        <p className="text-sm leading-6 text-red-100">
                          Delete removes this product and its product run records. Type the product name to confirm.
                        </p>
                        <input
                          value={deleteConfirmName}
                          onChange={(event) => setDeleteConfirmName(event.target.value)}
                          placeholder={product.name}
                          className="mt-3 w-full rounded-lg border border-red-500/40 bg-slate-950 px-3 py-2 text-sm text-white outline-none focus:border-red-300"
                        />
                        <div className="mt-3 flex flex-wrap gap-2">
                          <button
                            onClick={() => deleteProduct(product)}
                            disabled={busy || deleteConfirmName !== product.name}
                            className="rounded-lg bg-red-500 px-3 py-2 text-sm font-semibold text-white hover:bg-red-400 disabled:cursor-not-allowed disabled:opacity-60"
                          >
                            Confirm Delete
                          </button>
                          <button
                            onClick={() => {
                              setDeletingProductId(null);
                              setDeleteConfirmName("");
                            }}
                            className="rounded-lg border border-slate-700 px-3 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-800"
                          >
                            Cancel
                          </button>
                        </div>
                      </div>
                    ) : null}
                  </div>
                ))
              )}
            </div>
          </section>
        </div>

        <section className="mt-6 rounded-lg border border-slate-800 bg-slate-900/45 p-5">
          <div className="flex flex-col gap-2 sm:flex-row sm:items-end sm:justify-between">
            <div>
              <h2 className="text-xl font-semibold text-white">Starter Products</h2>
              <p className="mt-1 text-sm text-slate-400">Visible to all. These prefill product stages; current standalone Apps remain available.</p>
            </div>
            <button
              onClick={() => router.push("/apps")}
              className="rounded-lg border border-slate-700 px-3 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-800"
            >
              Open Apps
            </button>
          </div>

          <div className="mt-5 grid gap-4 md:grid-cols-2 xl:grid-cols-4">
            {references.map((reference) => (
              <article key={reference.slug} className="rounded-lg border border-slate-800 bg-slate-950/60 p-4">
                <div className="text-xs font-semibold uppercase text-cyan-300">{typeLabel(reference.product_type)}</div>
                <h3 className="mt-2 text-lg font-semibold text-white">{reference.name}</h3>
                <p className="mt-2 min-h-[72px] text-sm leading-6 text-slate-300">{reference.summary}</p>
                <div className="mt-4 space-y-2">
                  {(reference.definition.stages || []).slice(0, 5).map((stage) => (
                    <div key={stage.id} className="flex items-center justify-between gap-3 text-xs">
                      <span className="text-slate-300">{stage.label}</span>
                      <span className="rounded-md bg-slate-800 px-2 py-1 text-slate-400">{stageBadge(stage)}</span>
                    </div>
                  ))}
                </div>
                <button
                  onClick={() => {
                    setSelectedReference(reference.slug);
                    setProductName(reference.name);
                    setProductType((reference.product_type as ProductType) || "digital");
                    setDescription(reference.summary);
                    window.scrollTo({ top: 0, behavior: "smooth" });
                  }}
                  className="mt-4 w-full rounded-lg bg-slate-100 px-3 py-2 text-sm font-semibold text-slate-950 hover:bg-white"
                >
                  Use This Product
                </button>
              </article>
            ))}
          </div>
        </section>
      </div>
    </main>
  );
}
