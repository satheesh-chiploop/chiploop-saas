import json
from loguru import logger
from utils.llm_utils import run_llm_fallback
from utils.supabase_utils import supabase
from planner.ai_work_planner import analyze_spec
from datetime import datatime


async def fetch_user_memory(user_id: str):
    """Fetch user memory context from Supabase."""
    try:
        res = supabase.table("user_memory").select("*").eq("user_id", user_id).execute()
        if res.data:
            return res.data[0]
    except Exception as e:
        logger.warning(f"⚠️ Failed to fetch user_memory: {e}")
    return {"recent_goals": [], "frequent_agents": [], "preferred_style": ""}


async def fetch_agent_memory():
    """Fetch known agents and capabilities."""
    try:
        res = supabase.table("agent_memory").select("agent_name, capability_tags").execute()
        return res.data or []
    except Exception as e:
        logger.warning(f"⚠️ Failed to fetch agent_memory: {e}")
    return []


async def plan_agent_with_memory(goal: str, user_id: str = "anonymous") -> dict:
    """
    Agentic Agent Planner (Memory + Spec-Aware)
    1️⃣ Analyze spec
    2️⃣ Fetch memory context
    3️⃣ Generate agent plan or reuse from memory
    """

    logger.info(f"🧠 Planning agent with memory for goal: {goal}")

    # --- Step 1. Analyze spec
    try:
        coverage = await analyze_spec({"goal": goal, "user_id": user_id})
        total_score = coverage.get("total_score", 0)
        logger.info(f"📊 Spec coverage score: {total_score}%")
    except Exception as e:
        logger.warning(f"⚠️ Spec analysis failed: {e}")
        coverage = {
            "intent_score": 0,
            "io_score": 0,
            "constraint_score": 0,
            "verification_score": 0,
            "total_score": 0,
        }

    # --- Step 2. Fetch user + agent memory
    user_mem = await fetch_user_memory(user_id)
    agent_mem = await fetch_agent_memory()

    memory_context = {
        "recent_goals": user_mem.get("recent_goals", []),
        "frequent_agents": user_mem.get("frequent_agents", []),
        "preferred_style": user_mem.get("preferred_style", ""),
        "known_agents": [a["agent_name"] for a in agent_mem],
    }

    logger.info(f"🧩 Memory context: {memory_context}")

    # --- Step 3. Build planning prompt
    prompt = f"""
You are ChipLoop’s Agentic Agent Planner.
Your task is to design or reuse agents intelligently based on spec coverage and memory context.

Goal: {goal}

📊 Spec Coverage: {coverage.get('total_score', 0)}%
User Context:
- Recent Goals: {memory_context['recent_goals']}
- Frequent Agents: {memory_context['frequent_agents']}
- Preferred Style: {memory_context['preferred_style']}

Known Agents: {memory_context['known_agents']}

If an agent already exists with similar capability, suggest reusing or enhancing it.
Otherwise, create a new agent definition.

Return valid JSON only:
{{
  "agent_name": "",
  "description": "",
  "domain": "digital | analog | embedded",
  "capability_tags": [],
  "input_schema": "",
  "output_schema": "",
  "example_prompt": ""
}}
"""

    # --- Step 4. LLM Call
    response = await run_llm_fallback(prompt)

    # --- Step 5. Safe Parse
    try:
        start = response.find("{")
        end = response.rfind("}")
        if start != -1 and end != -1:
            response = response[start : end + 1]
        plan = json.loads(response)
    except Exception as e:
        logger.error(f"❌ JSON parse failed: {e} | Raw: {response[:200]}")
        plan = {
            "agent_name": "Unnamed_Agent",
            "description": response[:200],
            "domain": "unknown",
            "capability_tags": [],
        }

    # --- Step 6. Merge metadata
    plan["coverage"] = coverage
    plan["context_used"] = memory_context

    logger.info(f"✅ Agent plan ready: {plan.get('agent_name', 'Unnamed_Agent')}")
    return plan
    try:
        supabase.table("user_memory").upsert({
          "user_id": user_id,
          "recent_goals": list(set(memory_context.get("recent_goals", []) + [goal])),
          "frequent_agents": list(set(memory_context.get("frequent_agents", []) + [plan.get("agent_name")])),
          "updated_at": datetime.utcnow().isoformat(),
        }).execute()
        logger.info(f"🧠 Memory updated for user {user_id}")
    except Exception as e:
        logger.warning(f"⚠️ Failed to update user memory: {e}")