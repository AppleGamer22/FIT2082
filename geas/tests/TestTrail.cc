#include <iostream>
#include <cstdio>
#if 0
#include <geas/engine/trail.h>

int main(int argc, char** argv)
{
  Trail t;

  Trailed<int> i(&t, 0);

  fprintf(stdout, "Level: %d, i = %d\n\n", t.level(), (int) i);
  i = 7;

  fprintf(stdout, "Level: %d, i = %d\n\n", t.level(), (int) i);
  t.push_level();

  i = 18;
  fprintf(stdout, "Level: %d, i = %d\n", t.level(), (int) i);

  t.tick();

  i = 22;
  fprintf(stdout, "Level: %d, i = %d\n", t.level(), (int) i);

  t.push_level();
  i = 120;
  fprintf(stdout, "Level: %d, i = %d\n", t.level(), (int) i);

  t.restore_level();
  fprintf(stdout, "Level: %d, i = %d\n", t.level(), (int) i);

  i = 77;
  fprintf(stdout, "Level: %d, i = %d\n", t.level(), (int) i);

  t.restore_level();
  fprintf(stdout, "Level: %d, i = %d\n", t.level(), (int) i);

  return 0;
}
#endif
int main(int argc, char** argv) { return 0; }
