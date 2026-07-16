package cn.edu.nju.Iot_Verify;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.boot.autoconfigure.security.servlet.UserDetailsServiceAutoConfiguration;
import org.springframework.scheduling.annotation.EnableAsync;

@SpringBootApplication(exclude = UserDetailsServiceAutoConfiguration.class)
@EnableAsync
public class IotVerifyApplication {

	public static void main(String[] args) {
		SpringApplication.run(IotVerifyApplication.class, args);
	}

}
