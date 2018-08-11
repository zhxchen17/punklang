#include <vector>
#include <iostream>
#include <chrono>

const int len = 1000000;

int profile_a() {
  int sum = 0;
  std::vector<int*> a(len);
  for (int i=0; i<len; i++) {
    a[i] = new int;
  }

  std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
  for (int i=0; i<len; i++) {
    sum += *(a[i]);
  }
  std::chrono::steady_clock::time_point end= std::chrono::steady_clock::now();

  std::cout << "Time difference = " << std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count() << " ms." << std::endl;
  return sum;
}

int profile_b() {
  int sum = 0;
  std::vector<int*> a(len);
  std::vector<int> b(len);
  for (int i=0; i<len; i++) {
    a[i] = &(b[i]);
  }

  std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
  for (int i=0; i<len; i++) {
    sum += *(a[i]);
  }
  std::chrono::steady_clock::time_point end= std::chrono::steady_clock::now();

  std::cout << "Time difference = " << std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count() << " ms." <<std::endl;
  return sum;
}

struct Obj {
  char type;
  virtual ~Obj() {}
};

struct Int : public Obj {
  int i;
  Int() { type = 'i'; i = 0; }
};

struct Float : public Obj {
  float f;
  Float() { type = 'f'; f = 1; }
};

int profile_c() {
  int sum = 0;
  std::vector<Obj*> tp(len);
  for (int i=0; i<tp.size(); i++) {
    if (i%2)
      tp[i] = new Int;
    else
      tp[i] = new Float;
  }
  std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
  for (int i=0; i<tp.size(); i++) {
    Int* tmp = dynamic_cast<Int*>(tp[i]);
    if (tmp) sum += tmp->i;
  }
  std::chrono::steady_clock::time_point end= std::chrono::steady_clock::now();

  std::cout << "Time difference = " << std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count() << " ms." <<std::endl;
  return sum;
}

int profile_d() {
  int sum = 0;
  std::vector<Obj*> tp(len);
  for (int i=0; i<tp.size(); i++) {
    if (i%2)
      tp[i] = new Int;
    else
      tp[i] = new Float;
  }
  std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
  for (int i=0; i<tp.size(); i++) {
    if (tp[i]->type == 'i') {
      sum += reinterpret_cast<Int*>(tp[i])->i;
    }
  }
  std::chrono::steady_clock::time_point end= std::chrono::steady_clock::now();

  std::cout << "Time difference = " << std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count() << " ms." <<std::endl;
  return sum;
}

int profile_e() {
  for (int i=0; i<20; i++) {
    std::cout << sizeof(new short) << std::endl;
  }
}
int main() {
  std::cout << profile_e() << std::endl;
  return 0;
}
