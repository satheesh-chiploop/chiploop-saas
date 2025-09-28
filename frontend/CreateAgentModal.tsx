"use client";
import { useState } from "react";

export default function CreateAgentModal({ onClose, onCreated }: any) {
  const [name, setName] = useState("");
  const [desc, setDesc] = useState("");
  const [loading, setLoading] = useState(false);

  const handleSubmit = async () => {
    setLoading(true);
    const res = await fetch("http://127.0.0.1:8000/create_agent", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ name, description: desc }),
    });
    const data = await res.json();
    setLoading(false);
    onCreated(data);
    onClose();
  };

  return (
    <div className="fixed inset-0 bg-black/70 flex justify-center items-center z-50">
      <div className="bg-slate-900 p-6 rounded-lg w-96 shadow-xl">
        <h2 className="text-xl font-bold mb-4">➕ Create Custom Agent</h2>
        <input
          type="text"
          placeholder="Agent name"
          value={name}
          onChange={(e) => setName(e.target.value)}
          className="w-full mb-3 p-2 rounded bg-slate-800 text-white"
        />
        <textarea
          placeholder="Agent description"
          value={desc}
          onChange={(e) => setDesc(e.target.value)}
          className="w-full mb-3 p-2 rounded bg-slate-800 text-white"
        />
        <button
          onClick={handleSubmit}
          disabled={loading}
          className="w-full bg-cyan-500 text-black py-2 rounded hover:bg-cyan-400"
        >
          {loading ? "Creating..." : "Create Agent"}
        </button>
        <button
          onClick={onClose}
          className="w-full mt-2 bg-slate-700 py-2 rounded hover:bg-slate-600"
        >
          Cancel
        </button>
      </div>
    </div>
  );
}
