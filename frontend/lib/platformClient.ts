"use client";

/* eslint-disable @typescript-eslint/no-explicit-any */

import { createClientComponentClient as createSupabaseClient } from "@supabase/auth-helpers-nextjs";

const API_BASE = "/api";
const BACKEND_PROVIDER = "backend";

type QueryResult<T> = { data: T | null; error: any; count?: number | null };
type RealtimePayload = { new: any; old: any; eventType?: string };

export type PlatformClientLike = {
  auth: {
    getSession: () => Promise<{ data: { session: any | null }; error: any }>;
    getUser: (token?: string) => Promise<{ data: { user: any | null }; error: any }>;
    signOut: () => Promise<{ error: any }>;
    onAuthStateChange: (callback: (event: string, session: any | null) => void) => { data: { subscription: { unsubscribe: () => void } } };
    signUp: (credentials: any) => Promise<any>;
    signInWithPassword: (credentials: any) => Promise<any>;
    signInWithOtp: (credentials: any) => Promise<any>;
  };
  from: <T = any>(table: string) => BackendQueryBuilder<T>;
  channel: (name: string) => BackendChannel;
  removeChannel: (channel: BackendChannel) => void;
  storage: any;
};

export function usesBackendPlatform(): boolean {
  return (process.env.NEXT_PUBLIC_CHIPLOOP_PLATFORM_PROVIDER || "supabase").toLowerCase() === BACKEND_PROVIDER;
}

async function request(path: string, init?: RequestInit): Promise<any> {
  const token = typeof window !== "undefined" ? window.localStorage.getItem("chiploop_access_token") : null;
  const headers = new Headers(init?.headers || {});
  if (token) headers.set("Authorization", `Bearer ${token}`);
  if (init?.body && !headers.has("Content-Type")) headers.set("Content-Type", "application/json");
  const response = await fetch(`${API_BASE}${path}`, { ...init, headers, credentials: "include", cache: "no-store" });
  const text = await response.text();
  const data = text ? JSON.parse(text) : null;
  if (!response.ok) throw new Error(typeof data?.detail === "string" ? data.detail : `Request failed with status ${response.status}`);
  return data;
}

class BackendQueryBuilder<T = any> implements PromiseLike<QueryResult<T | T[]>> {
  private spec: Record<string, any>;

  constructor(table: string) {
    this.spec = { table, operation: "select", columns: "*", filters: [], orders: [] };
  }

  select(columns = "*", options?: { count?: string }) {
    this.spec.operation = "select";
    this.spec.columns = columns;
    this.spec.count = options?.count;
    return this;
  }

  insert(payload: any) { this.spec.operation = "insert"; this.spec.payload = payload; return this; }
  update(payload: any) { this.spec.operation = "update"; this.spec.payload = payload; return this; }
  upsert(payload: any, options?: { onConflict?: string }) {
    this.spec.operation = "upsert";
    this.spec.payload = payload;
    this.spec.on_conflict = options?.onConflict;
    return this;
  }
  delete() { this.spec.operation = "delete"; return this; }

  private filter(method: string, column: string, value: any) {
    this.spec.filters.push({ method, column, value });
    return this;
  }

  eq(column: string, value: any) { return this.filter("eq", column, value); }
  neq(column: string, value: any) { return this.filter("neq", column, value); }
  gt(column: string, value: any) { return this.filter("gt", column, value); }
  gte(column: string, value: any) { return this.filter("gte", column, value); }
  lt(column: string, value: any) { return this.filter("lt", column, value); }
  lte(column: string, value: any) { return this.filter("lte", column, value); }
  in(column: string, value: any[]) { return this.filter("in_", column, value); }
  is(column: string, value: any) { return this.filter("is_", column, value); }
  or(expression: string) { this.spec.filters.push({ method: "or_", value: expression }); return this; }

  order(column: string, options?: { ascending?: boolean }) {
    this.spec.orders.push({ column, ascending: options?.ascending !== false });
    return this;
  }

  limit(value: number) { this.spec.limit = value; return this; }
  single<TSingle = T>() { this.spec.single = true; return this as unknown as PromiseLike<QueryResult<TSingle>>; }
  maybeSingle<TSingle = T>() { this.spec.maybe_single = true; return this as unknown as PromiseLike<QueryResult<TSingle>>; }

  async execute() {
    try {
      return await request("/platform/query", { method: "POST", body: JSON.stringify(this.spec) });
    } catch (error) {
      return { data: null, count: null, error };
    }
  }

  then<TResult1 = QueryResult<T | T[]>, TResult2 = never>(
    onfulfilled?: ((value: QueryResult<T | T[]>) => TResult1 | PromiseLike<TResult1>) | null,
    onrejected?: ((reason: any) => TResult2 | PromiseLike<TResult2>) | null,
  ): PromiseLike<TResult1 | TResult2> {
    return this.execute().then(onfulfilled, onrejected);
  }
}

class BackendChannel {
  private timer: ReturnType<typeof setInterval> | null = null;
  private table = "";
  private filterValue = "";
  private callback: ((payload: RealtimePayload) => void) | null = null;
  private last = "";

  on(_event: string, options: { table?: string; filter?: string; [key: string]: any }, callback: (payload: RealtimePayload) => void) {
    this.table = options.table || "";
    this.filterValue = options.filter || "";
    this.callback = callback;
    return this;
  }

  subscribe() {
    const poll = async () => {
      if (!this.table || !this.callback) return;
      const query = new BackendQueryBuilder(this.table).select("*");
      const match = this.filterValue.match(/^([^=]+)=eq\.(.+)$/);
      if (match) query.eq(match[1], match[2]);
      const result = await query.maybeSingle();
      const serialized = JSON.stringify(result.data ?? null);
      if (serialized !== this.last) {
        this.last = serialized;
        if (result.data) this.callback({ new: result.data, old: null, eventType: "UPDATE" });
      }
    };
    void poll();
    this.timer = setInterval(poll, Number(process.env.NEXT_PUBLIC_CHIPLOOP_POLL_INTERVAL_MS || 2000));
    return this;
  }

  unsubscribe() {
    if (this.timer) clearInterval(this.timer);
    this.timer = null;
  }
}

function backendAuth() {
  return {
    async getSession() {
      try {
        const data = await request("/platform/session");
        return { data: { session: data?.user ? { user: data.user, access_token: null } : null }, error: null };
      } catch (error) {
        return { data: { session: null }, error };
      }
    },
    async getUser(token?: string) {
      void token;
      const result = await this.getSession();
      return { data: { user: result.data.session?.user || null }, error: result.error };
    },
    async signOut() {
      if (typeof window !== "undefined") window.localStorage.removeItem("chiploop_access_token");
      await fetch("/auth/logout", { method: "POST", credentials: "include" });
      return { error: null };
    },
    onAuthStateChange(callback: (event: string, session: any) => void) {
      let active = true;
      void this.getSession().then((result) => {
        if (active) callback(result.data.session ? "SIGNED_IN" : "SIGNED_OUT", result.data.session);
      });
      return { data: { subscription: { unsubscribe: () => { active = false; } } } };
    },
    async signUp(credentials: any) { void credentials; return { data: null, error: new Error("Sign-up is managed by the configured identity provider.") }; },
    async signInWithPassword(credentials: any) { void credentials; return { data: null, error: new Error("Password sign-in is managed by the configured identity provider.") }; },
    async signInWithOtp(credentials: any) { void credentials; return { data: null, error: new Error("Magic-link sign-in is managed by the configured identity provider.") }; },
  };
}

function createBackendClient(): PlatformClientLike {
  return {
    auth: backendAuth(),
    from: (table: string) => new BackendQueryBuilder(table),
    channel: (name: string) => { void name; return new BackendChannel(); },
    removeChannel: (channel: BackendChannel) => channel.unsubscribe(),
    storage: {
      from: (bucket: string) => ({
        download: async (path: string) => {
          const response = await fetch(`${API_BASE}/platform/storage/${encodeURIComponent(bucket)}/${path}`, { credentials: "include" });
          return { data: response.ok ? await response.blob() : null, error: response.ok ? null : new Error(await response.text()) };
        },
      }),
    },
  };
}

let singleton: PlatformClientLike | undefined;

export function createClientComponentClient(): PlatformClientLike {
  if (!singleton) singleton = usesBackendPlatform() ? createBackendClient() : createSupabaseClient() as unknown as PlatformClientLike;
  return singleton;
}

export const platformClient = createClientComponentClient();
