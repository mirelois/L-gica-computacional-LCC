from pysmt.shortcuts import *
from pysmt.typing import INT
import random as rn

N = 5

l = [[0 for x in range(N)] for y in range(N)]

l[2][3] = 1

from pylab import *
A = rand(5,5)
figure(1)
imshow(l)
grid(True)

import matplotlib.pyplot as plt
import numpy as np

# a 2D array with linearly increasing values on the diagonal
a = np.diag(range(15))

plt.matshow(l)

plt.show()