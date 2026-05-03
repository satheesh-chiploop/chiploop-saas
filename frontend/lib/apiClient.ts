"use client";

import { createClientComponentClient } from "@supabase/auth-helpers-nextjs";

const API_BASE = "/api";

export class ApiClientError extends Error {
  status: number;
  detail: unknown;

  constructor(message: string, status: number, detail?: unknown) {
    super(message);
    this.name = "ApiClientError";
    this.status = status;
    this.detail = detail;
  }
}

async function authHeaders(): Promise<Record<string, string>> {
  const supabase = createClientComponentClient();
  const {
    data: { session },
  } = await supabase.auth.getSession();

  if (!session?.access_token) return {};
  return { Authorization: `Bearer ${session.access_token}` };
}

async function request<T>(method: "GET" | "POST", path: string, body?: unknown): Promise<T> {
  const headers: Record<string, string> = {
    ...(await authHeaders()),
  };

  if (body !== undefined) {
    headers["Content-Type"] = "application/json";
  }

  const response = await fetch(`${API_BASE}${path}`, {
    method,
    headers,
    body: body === undefined ? undefined : JSON.stringify(body),
    cache: "no-store",
  });

  const text = await response.text();
  let data: unknown = null;
  if (text) {
    try {
      data = JSON.parse(text);
    } catch {
      data = { detail: text };
    }
  }

  if (!response.ok) {
    const responseObject = data && typeof data === "object" ? (data as Record<string, unknown>) : null;
    const detail = responseObject && "detail" in responseObject ? responseObject.detail : data;
    const detailMessage =
      detail && typeof detail === "object" && "message" in detail && typeof detail.message === "string"
        ? detail.message
        : null;
    const message =
      typeof detail === "string"
        ? detail
        : detailMessage
        ? detailMessage
        : responseObject && typeof responseObject.error === "string"
        ? responseObject.error
        : `Request failed with status ${response.status}`;
    throw new ApiClientError(message, response.status, detail);
  }

  return data as T;
}

export function apiGet<T>(path: string): Promise<T> {
  return request<T>("GET", path);
}

export function apiPost<T>(path: string, body?: unknown): Promise<T> {
  return request<T>("POST", path, body ?? {});
}
