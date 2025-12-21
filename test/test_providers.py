from src.llm.providers import GeminiProvider, OpenAICompatibleProvider, VLLMProvider



def test_gemini():
    provider = GeminiProvider()
    mtchat = provider.new_chat(model="gemini-3-flash-preview", system_prompt="You are a helpful assistant.")
    
    res = mtchat.send_message("Hello, how are you?")
    print(res['text'])
    res = mtchat.send_message("Can you write a short poem about the stars?")
    print(res['text'])
    print(mtchat.get_total_tokens())
    print(mtchat.get_total_tokens().total_tokens)
    print(type(mtchat.get_total_tokens().total_tokens))

def test_openai():
    provider = OpenAICompatibleProvider()
    mtchat = provider.new_chat(model="gpt-4o", system_prompt="You are a helpful assistant.")
    
    res = mtchat.send_message("Hello, how are you?")
    print(res['text'])
    res = mtchat.send_message("Can you write a short poem about the stars?")
    print(res['text'])
    print(mtchat.get_total_price())

def test_vllm():
    provider = VLLMProvider(endpoint="http://della-k12g1:45491/v1")
    mtchat = provider.new_chat(model='/scratch/gpfs/ARORA/haoyu/Qwen3-32B', system_prompt="You are a helpful assistant.")
    
    res = mtchat.send_message("Hello, how are you?")
    print(res['text'])
    res = mtchat.send_message("Can you write a short poem about the stars?")
    print(res['text'])
    print(mtchat.get_total_price())

if __name__ == "__main__":
    test_gemini()
