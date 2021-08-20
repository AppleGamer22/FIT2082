# LazyCBS - miscellaneous scripts

### map-conv.py - movingai.com benchmark map converter
LazyCBS (at present) expects maps in the same form as ECBS, which differs
from the [movingai.com](https://movingai.com/benchmarks/mapf.html) benchmarks repository.
`map-conv.py` is a quick and dirty (Python 2) script to do the conversion.

To run movingai scenarios, you will first need to convert the map:
   ```map-conv.py < [movingai-map.map] > [movingai-map.map.ecbs]```
then you can use LazyCBS with the existing scenario files and the `--upto` flag (to specify the number of agents):
   ```map-conv.py --map [movingai-map.map.ecbs] --agents [movingai-map-scenario.scen] --upto [count]```
