from __future__ import annotations

import json
import os
from abc import ABC, abstractmethod
from pathlib import Path
from typing import Dict, List, Optional
from urllib import request


class LLMProvider(ABC):
    @abstractmethod
    def generate(self, prompt: str, metadata: Optional[Dict[str, str]] = None) -> str:
        raise NotImplementedError


class ReplayProvider(LLMProvider):
    """Deterministic provider that replays pre-authored outputs from disk."""

    def __init__(self, replay_dir: str):
        self._files: List[Path] = sorted(Path(replay_dir).glob("*.tla"))
        self._index = 0
        if not self._files:
            raise ValueError(f"No .tla replay files found in: {replay_dir}")

    def generate(self, prompt: str, metadata: Optional[Dict[str, str]] = None) -> str:
        _ = prompt
        _ = metadata
        file_path = self._files[min(self._index, len(self._files) - 1)]
        self._index += 1
        return file_path.read_text(encoding="utf-8")


class OpenAICompatibleProvider(LLMProvider):
    """Simple OpenAI-compatible chat-completion client using stdlib urllib."""

    def __init__(self, model: str, base_url: str = "https://api.openai.com/v1"):
        self.model = model
        self.base_url = base_url.rstrip("/")
        self.api_key = os.environ.get("OPENAI_API_KEY", "")
        if not self.api_key:
            raise ValueError("OPENAI_API_KEY is not set.")

    def generate(self, prompt: str, metadata: Optional[Dict[str, str]] = None) -> str:
        _ = metadata
        body = {
            "model": self.model,
            "messages": [
                {
                    "role": "system",
                    "content": "You produce only valid TLA+ code with no markdown fences.",
                },
                {"role": "user", "content": prompt},
            ],
            "temperature": 0.0,
        }

        endpoint = f"{self.base_url}/chat/completions"
        data = json.dumps(body).encode("utf-8")
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {self.api_key}",
        }

        req = request.Request(endpoint, data=data, headers=headers, method="POST")
        with request.urlopen(req, timeout=90) as response:
            payload = json.loads(response.read().decode("utf-8"))

        return payload["choices"][0]["message"]["content"].strip()


def build_provider(provider_name: str, model: str, replay_dir: Optional[str]) -> LLMProvider:
    if provider_name == "replay":
        if not replay_dir:
            raise ValueError("--replay-dir is required when provider is replay")
        return ReplayProvider(replay_dir)

    if provider_name == "openai":
        return OpenAICompatibleProvider(model=model)

    raise ValueError(f"Unsupported provider: {provider_name}")
