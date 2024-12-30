import string, random 
# from config import Config

class RandomGenerator(): 
    def __init__(self, write_to_: str, file_size_target_: int): 
        self.write_to = write_to_
        self.file_size_target = file_size_target_ 
        self.char_pool = string.ascii_lowercase + string.ascii_uppercase + string.digits + string.punctuation
        
    def generate_random_input_alphanumerical(self) -> str: 
            self.generate_alphanumerical_helper(self.write_to, self.file_size_target)
    
    def generate_alphanumerical_helper(self, write_to: str, file_size: int) -> str: 
            bytes_written = 0 
            
            with open(write_to, "w") as rand_file: 
                while bytes_written < file_size: 
                    line_len = random.randint(1,32) 
                    sentence = self.generate_random_sentence(line_len)
                    rand_file.write(sentence + '\n')
                    bytes_written += line_len + 1
    
    def generate_random_sentence(self, line_len: int) -> str:
        curr_line_len = 0 
        sentence = ""
        while curr_line_len < line_len: 
            word_len = random.randint(1,line_len) 
            word = ''.join(random.choices(self.char_pool, k=word_len))
            sentence += word + " "
            curr_line_len += len(word) + 1 

        return sentence
        
                    
                    
    # def generate_random_input(self, write_to: str, file_size: int, configuration: Config): 
    #     return 
           
                
