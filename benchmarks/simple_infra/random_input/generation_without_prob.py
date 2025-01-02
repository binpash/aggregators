import string, random
import numpy as np

class RandomGeneratorSimple(): 
    def __init__(self, write_to_: str, file_size_target_: int, min_byte_per_line_: int, max_byte_per_line_: int): 
        self.write_to = write_to_
        self.file_size_target = file_size_target_ 
        self.min_bytes_per_line = min_byte_per_line_ 
        self.max_bytes_per_line = max_byte_per_line_
        self.char_pool = string.ascii_lowercase + string.ascii_uppercase + string.digits + string.punctuation
        
    def generate(self): 
        text = self.generate_text_full_random(self.file_size_target, self.min_bytes_per_line, self.max_bytes_per_line)
        if self.write_to != "": 
            self.write_text_to_file(text)
        return text 
        
    def write_text_to_file(self, text: list[str]):
         with open(self.write_to, "w") as rand_file:  
            for line in text: 
                rand_file.write(line)
            
    def generate_text_full_random(self, file_size: int, min_byte_per_line: int, max_byte_per_line: int) -> str: 
        bytes_left = file_size 
        
        text = ""
        while bytes_left > 0: 
            if bytes_left == 1:
                text += '\n'
                break 
            
            line_len = random.randint(min_byte_per_line, min(max_byte_per_line, bytes_left - 1))
            sentence = self.generate_random_sentence(line_len)
            sentence += '\n'
            bytes_left -= line_len + 1
            text += sentence
        
        np.testing.assert_equal(len(text), self.file_size_target)
        return text

    def generate_random_sentence(self, line_len: int) -> str:
        curr_line_len = 0 
        sentence = ""
        while curr_line_len < line_len: 
            max_word_len = line_len - curr_line_len
            word_len = random.randint(1, max_word_len)
            word = ''.join(random.choices(self.char_pool, k=word_len - 1))
            sentence += word + " "
            curr_line_len += len(word) + 1
        np.testing.assert_equal(len(sentence), line_len)
        return sentence 

if __name__ == "__main__":
    total_bytes = 10000
    rand_generator = RandomGeneratorSimple("rand.txt", total_bytes, 1, 32) 
    rand_generator.generate()
    
    