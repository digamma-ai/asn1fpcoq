unsigned int factorial (unsigned int input) {
  unsigned int output = 1;
  while (input){
      output = output*input ;
      input = input - 1 ;
    } 
  return output ;
}

