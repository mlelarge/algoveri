from src.llm.providers import GeminiProvider



def test_gemini():
    provider = GeminiProvider()
    mtchat = provider.new_chat(model="gemini-2.5-flash", system_prompt="You are a helpful assistant.")
    
    res = mtchat.send_message("Hello, how are you?")
    print(res['text'])
    res = mtchat.send_message("Can you write a short poem about the stars?")
    print(res['text'])
    print(mtchat.get_total_price())

if __name__ == "__main__":
    test_gemini()
