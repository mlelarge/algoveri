"""Provider implementations for different LLM backends.

This file exposes a message-first ProviderBase and two concrete adapters:
- OpenAICompatibleProvider: uses `openai.OpenAI` client (can be pointed to Google
  GenAI by using the OpenAI-compatible base_url).
- GeminiProvider: prefers `google.genai` client, falls back to the OpenAI-compatible adapter.
"""
from typing import Any, Dict, List, Optional
import os
import logging

# Multi-round chat abstractions

class MultiTurnChat:
    """Abstract multi-turn chat session.

    Methods:
      - send_message(text, role='user') -> dict with 'text' and 'role'
      - get_history() -> list[dict] with keys ('role','content', ...)
      - close() -> optional cleanup
    """
    def send_message(self, text: str, role: str = "user") -> Dict[str, Any]:
        raise NotImplementedError()

    def get_history(self) -> List[Dict[str, Any]]:
        raise NotImplementedError()
    
    def get_total_price(self) -> float:
        raise NotImplementedError()

    def close(self) -> None:
        return None


class ProviderBase:
    """Provider that can create multi-turn chat sessions."""
    name: str = "base"

    def __init__(self, **kwargs: Any):
        self.config = kwargs
        self.logger = logging.getLogger(self.__class__.__name__)

    def new_chat(self, *, model: str = "", system_prompt: Optional[str] = None, **kwargs: Any) -> MultiTurnChat:
        """Create a new multi-turn chat session for the provider."""
        raise NotImplementedError()

    def close(self) -> None:
        return None


# OpenAI-compatible adapter intentionally omitted / unimplemented
class OpenAICompatibleProvider(ProviderBase):
    name = "openai_compatible"

    def __init__(self, *args: Any, **kwargs: Any):
        super().__init__(*args, **kwargs)

    def new_chat(self, *args: Any, **kwargs: Any) -> MultiTurnChat:
        raise NotImplementedError("OpenAI-compatible provider is not implemented in this adapter.")


# Gemini implementation (google.genai preferred)
class GeminiMultiTurnChat(MultiTurnChat):
    def __init__(self, genai_chat: Any, model_name: str = "", genai_client: Optional[Any] = None):
        self._chat = genai_chat
        self._client = genai_client
        self._model_name = model_name

    def send_message(self, text: str, role: str = "user") -> Dict[str, Any]:
        """
        Send a message into the underlying gemini/genai chat session.
        Returns a dict: {'text': <assistant text>, 'role': 'assistant', 'raw': <raw response>}
        """
        # genai.Client.chat.send_message returns an object with .text per user's snippet
        resp = self._chat.send_message(text)
        text_out = getattr(resp, "text", None) or (resp.get("text") if isinstance(resp, dict) else str(resp))
        return {"text": text_out, "role": "assistant", "raw": resp}

    def get_history(self) -> List[Dict[str, Any]]:
        """Return history in normalized form: list of {'role':..., 'content':...}"""
        hist = []
        try:
            for message in self._chat.get_history():
                role = getattr(message, "role", None) or (message.get("role") if isinstance(message, dict) else None)
                # message.parts[0].text in your snippet; handle objects/dicts
                content = None
                try:
                    parts = getattr(message, "parts", None) or (message.get("parts") if isinstance(message, dict) else None)
                    if parts:
                        first = parts[0]
                        content = getattr(first, "text", None) or (first.get("text") if isinstance(first, dict) else None)
                except Exception:
                    content = None
                # fallback: try message.text
                if content is None:
                    content = getattr(message, "text", None) or (message.get("text") if isinstance(message, dict) else None)
                hist.append({"role": role or "unknown", "content": content})
        except Exception:
            # If underlying client doesn't support get_history or fails, return empty
            pass
        return hist
    
    def get_total_price(self):
        return self._client.models.count_tokens(model=self._model_name, contents=self._chat.get_history()) if self._client else 0.0

    def close(self) -> None:
        # genai chat objects currently do not require explicit close; keep for API parity
        return None


class GeminiProvider(ProviderBase):
    """Gemini provider using google.genai; falls back to raising error if unavailable."""
    name = "gemini"

    def __init__(self, api_key: Optional[str] = None, **kwargs: Any):
        super().__init__(api_key=api_key, **kwargs)
        self.logger = logging.getLogger("GeminiProvider")
        self._genai = None
        self._client = None
        self._api_key = api_key or os.environ.get("GEMINI_API_KEY") or os.environ.get("GENAI_API_KEY")

        try:
            from google import genai  # type: ignore
            self._genai = genai
            try:
                if self._api_key:
                    self._client = genai.Client(api_key=self._api_key)
                else:
                    self._client = genai.Client()
            except TypeError:
                self._client = genai.Client()
        except Exception as e:
            self.logger.debug("google.genai import failed: %s", e)
            self._genai = None
            self._client = None

    def new_chat(self, *, model: str = "gemini-2.5-flash", system_prompt: Optional[str] = None, **kwargs: Any) -> MultiTurnChat:
        if self._client is None:
            raise RuntimeError("google.genai client not available; install google-genai and set GEMINI_API_KEY/GENAI_API_KEY")

        # create chat and optionally send a system prompt
        chat = self._client.chats.create(model=model)
        mtchat = GeminiMultiTurnChat(chat, model_name=model, genai_client=self._client)
        if system_prompt:
            # use send_message with role system if client doesn't support it natively,
            # we simply send the system prompt first (client may treat first message as system)
            try:
                # some genai versions support chat.send_message with role; try best-effort
                if hasattr(chat, "send_message"):
                    mtchat.send_message(system_prompt, role="system")
            except Exception:
                # ignore failures for system prompt injection
                self.logger.debug("failed to send system_prompt to gemini chat (non-fatal)")
        return mtchat

    def close(self) -> None:
        # nothing to close at provider level
        return None


class VLLMProvider(ProviderBase):
    def __init__(self, endpoint: Optional[str] = None, **kwargs: Any):
        super().__init__(endpoint=endpoint, **kwargs)

    def new_chat(self, *args: Any, **kwargs: Any) -> MultiTurnChat:
        raise NotImplementedError("vLLM multi-turn chat not implemented in this adapter.")
