import re



str = ''

input = open('testfile3', 'r')

for linha in input:
    str += linha
    
print(str)

col = re.findall(r"A = True\nB = False\nC = False\nD = False", str)

print(col)